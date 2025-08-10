%% Copyright 2013-2014 Viktor Söderqvist
%% Copyright 2025 Andy (https://github.com/m-2k)
%%
%% Licensed under the Apache License, Version 2.0 (the "License");
%% you may not use this file except in compliance with the License.
%% You may obtain a copy of the License at
%%
%%     http://www.apache.org/licenses/LICENSE-2.0
%%
%% Unless required by applicable law or agreed to in writing, software
%% distributed under the License is distributed on an "AS IS" BASIS,
%% WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
%% See the License for the specific language governing permissions and
%% limitations under the License.

%% @doc JSON-RPC 2.0 client
-module(jsonrpc2_client).

-include_lib("kernel/include/logger.hrl").

-export_type([
	request_spec/0,
	transport_fn/0,
	response/0
]).

-export([
	call/2,
	multi_call/3
]).


-type request_id() :: atom() | binary() | integer() | null | auto. % auto – internal option, uses only with multi_call/3
-type request_method() :: atom() | binary().
-type request_params() :: [ json:encode_value() ] | #{ binary() | atom() | integer() => json:encode_value() }.
-type request_context() :: any().

-type call_request() :: #{
	id := request_id(),
	method := request_method(),
	params => request_params(),
	context => request_context()
}.

-type notification_request() :: #{
	method := request_method(),
	params => request_params(),
	context => request_context()
}.

-type request_spec() :: call_request() | notification_request().
-type transport_fn() :: fun ((iodata()) -> binary()).

-type error_response() ::
	#{
		code => integer(),
		message => binary(),
		data => json:decode_value()}
	| #{
		code => integer(),
		message => binary()}.

-type response() ::
	{ok, json:decode_value()}
	| {error, {invalid_response, json:decode_value()}}
	| {error, {error_response, error_response()}}.


-spec call(RequestSpec :: request_spec(), TransportFn :: transport_fn()) -> response().
call(RequestSpec, TransportFn) ->
	Req = request(RequestSpec),
	maybe
		{ok, ReqBin} ?= safe_eval(json_encoder, json, encode, [Req]),
		{ok, RespBin} ?= safe_eval(transport, TransportFn, [ReqBin]),
		{ok, ReqId} ?= case Req of #{id := Id} -> {ok, Id}; #{} -> ok end, % notification
		{ok, Resp} ?= safe_eval(json_decoder, json, decode, [RespBin]),
		{ok, _Result} ?= parse_response(Resp, [ReqId])
	else
		 Result -> Result
	end.


-spec multi_call(RequestSpecs :: [ request_spec() ], TransportFn :: transport_fn(), AutoIdStart :: integer()) -> response().
multi_call(RequestSpecs, TransportFn, AutoIdStart) ->
	{SpecsWithId, _} = lists:mapfoldl(fun
		(RS = #{id := auto}, Id) -> {RS#{id => Id}, Id + 1};
		(RS, Id) -> {RS, Id}
	end, AutoIdStart, RequestSpecs),
	Ids = [ Id || #{id := Id} <- SpecsWithId ],
	Req = [ request(RS) || RS <- SpecsWithId],
	
	maybe
		{ok, ReqBin} ?= safe_eval(json_encoder, json, encode, [Req]),
		{ok, RespBin} ?= safe_eval(transport, TransportFn, [ReqBin]),
		{ok, _} ?= case RespBin of <<>> -> ok; _ -> {ok, RespBin} end, % empty reply
		{ok, Resp} ?= safe_eval(json_decoder, json, decode, [RespBin]),
		case Resp of
			[_|_] ->
				[ begin
					Ctx = find_context(R, SpecsWithId),
					list_to_tuple(tuple_to_list(parse_response(R, Ids)) ++ [Ctx])
				end || R <- Resp ]
		end
	else
		Result -> Result
	end.


find_context(#{~"id" := Id} = _Resp, SpecsWithId) ->
	Search = fun
		(#{id := SpecId}) -> SpecId =:= Id;
		(#{ }) -> false
	end,
	case lists:search(Search, SpecsWithId) of
		{value, #{ context := Context}} -> Context;
		_ -> undefined
	end;
find_context(#{} = _Resp, _SpecsWithId) ->
	undefined.


request(#{method := Mtd} = RequestSpec) ->
	Method = case RequestSpec of
		#{module := Mod} -> <<(atom_to_binary(Mod))/binary, $:, (atom_to_binary(Mtd))/binary>>;
		_ -> Mtd
	end,
	_Req = maps:merge(#{jsonrpc => ~"2.0", method => Method}, maps:with([id, params], RequestSpec)).


safe_eval(Scope, F, A) ->
	safe_eval(Scope, erlang, apply, [F, A]).

safe_eval(Scope, M, F, A) ->
	try {ok, erlang:apply(M, F, A)}
	catch Class:Reason:Stacktrace ->
		?LOG_ERROR("Error: ~tp ~tp ~tp", [Class, Reason, Stacktrace]),
		{error, {Scope, Reason}}
	end.


parse_response(R = #{
	~"jsonrpc" := ~"2.0",
	~"id" := Id,
	~"error" := #{~"code" := Code, ~"message" := <<Message/binary>>} = Error
}, Ids) when is_integer(Code) ->
	case lists:member(Id, Ids) orelse Id =:= null of
		true ->
			Err = #{code => Code, message => Message},
			ErrB = case Error of
				#{data := Data} -> Err#{data => Data};
				_ -> Err
			end,
			{error, {error_response, ErrB}};
		false ->
			{error, {invalid_response, R}}
	end;

parse_response(R = #{
	~"jsonrpc" := ~"2.0",
	~"id" := Id,
	~"result" := Result
}, Ids) ->
	case lists:member(Id, Ids) orelse Id =:= null of
		true ->
			{ok, Result};
		false ->
			{error, {invalid_response, R}}
	end;

parse_response(R, _Ids) ->
	{error, {invalid_response, R}}.


%%------------
%% Unit tests
%%------------

-ifdef(TEST).


-include_lib("eunit/include/eunit.hrl").


test_handler(<<"add">>, [A, B]) -> {ok, A+B};
test_handler(<<"notify">>, []) -> ok.


test_transport(Req) ->
	case jsonrpc2:handle(Req, fun test_handler/2) of
		{reply, Reply} -> iolist_to_binary(Reply);
		noreply -> <<>>
	end.


call__1_test() ->
	?assertEqual({ok, 7}, call(#{id => 1, method => add, params => [-1,8]}, fun test_transport/1)),
	?assertEqual(ok,      call(#{         method => add, params => [-1,8]}, fun test_transport/1)).


call_2_test() ->
	?assertEqual({ok, 7}, call(#{id => 1, method => add, params => [-1,8]}, fun test_transport/1)),
	?assertEqual(ok,      call(#{         method => notify}, fun test_transport/1)).


multi_call_1_test() ->
	Req = [ #{id => 1, method => add, params => [-1,8]} ],
	?assertEqual([{ok, 7, undefined}], multi_call(Req, fun test_transport/1, 1)).


multi_call_2_test() ->
	Ctx = #{ctx => 3000},
	Req = [ #{id => 1, method => add, params => [-1,8], context => Ctx} ],
	?assertEqual([{ok, 7, Ctx}], multi_call(Req, fun test_transport/1, 1)).


multi_call_3_test() ->
	Req = [
		#{id => auto, method => add, params => [-1,8], context =>  #{ctx => 1000}},
		#{id => auto, method => add, params => [-1,9], context =>  #{ctx => 2000}},
		#{id => auto, method => add, params => [-1,10], context =>  #{ctx => 3000}}
	],
	?assertEqual([
		{ok, 7, #{ctx => 1000}},
		{ok, 8, #{ctx => 2000}},
		{ok, 9, #{ctx => 3000}}
	], multi_call(Req, fun test_transport/1, 10)).


multi_call_4_test() ->
	Req = [
		#{id => auto, method => add,   params => [-1,8]},
		#{            method => notify                 }
	],
	?assertEqual([ {ok, 7, undefined} ], multi_call(Req, fun test_transport/1, 10)).


multi_call_5_test() ->
	Req = [
		#{id =>  98, method => add,   params => [98,0],  context => a},
		#{           method => notify,                   context => c},
		#{id => -98, method => add,   params => [0,-98], context => b}
	],
	?assertEqual([ {ok, 98, a}, {ok, -98, b} ], multi_call(Req, fun test_transport/1, 10)).


multi_call_6_test() ->
	Req = [ #{method => add, params => [-1,8]} ],
	?assertEqual(ok, multi_call(Req, fun test_transport/1, 1)).


-endif.
