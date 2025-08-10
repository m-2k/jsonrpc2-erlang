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

-module(jsonrpc2).

-include_lib("kernel/include/logger.hrl").

-export([
    handle/2,
    handle/3,
    handle/4,
    handle_term/2,
    handle_term/3,
    handle_term/4
]).

-define(MF_SEP, [<<":">>, <<".">>]).
-define(OPAQUE_CTX(Opaque), {opaque, Opaque}).
-define(WITHOUT_OPAQUE, undefined).
-define(ENCODE(Term), json:encode(Term)).
-define(DECODE(Data), case Data of <<Data/binary>> -> json:decode(Data); Data -> json:decode(iolist_to_binary(Data)) end).


-export_type([
  pre_defined_error/0,
  handle_body/0,
  handle_term/0,
  handler/0,
  map_handler/0,
  internal_request/0,
  internal_request_finished/0
]).

-type pre_defined_error() ::
  parse_error
  | invalid_request
  | method_not_found
  | invalid_params
  | internal_error
  | server_error. 

-type internal_request() :: #{
  module => atom(),
  function_name := atom(),
  params := #{ binary() => json:decode_value() } | [ json:decode_value() ] % this will be an empty list if the field "params" were omitted in the original request
}.

-type internal_request_finished() :: #{
  module => atom(),
  function_name := atom(),
  result | error := any()
}.

-type handle_body() :: iodata().
-type handle_term() :: json:decode_value().
-type handler_fn() :: fun((Method :: binary(), Params :: json:decode_value()) ->
  ok
  | {ok, Result :: any()}
  | {error, pre_defined_error() | Reason :: any()}
).

-type handler_with_opaque_fn() :: fun((Method :: binary(), Params :: json:decode_value(), OpaqueIn :: opaque()) ->
  ok
  | {ok, Result :: any()}
  | {ok, Result :: any(), OpaqueOut :: opaque()}
  | {error, pre_defined_error() | Reason :: any()}
  | {error, pre_defined_error() | Reason :: any(), OpaqueOut :: opaque()}
).

-type modules_white_list_and_overrides() :: #{ ModuleFromMethod :: binary() => ModuleOverride :: module() }.
-type handler() :: handler_fn() | module() | modules_white_list_and_overrides().
-type handler_with_opaque() :: handler_with_opaque_fn() | module() | modules_white_list_and_overrides().
-type opaque() :: any().
-type map_handler_fn() ::fun((internal_request(), opaque()) -> {internal_request_finished(), opaque()}).
-type map_handler() :: fun((map_handler_fn(), opaque(), [internal_request()]) -> {[internal_request_finished()], opaque()}).


-spec handle(Body :: handle_body(), Handler :: handler()) -> {reply, Reply :: iodata()} | noreply.
handle(Body, Handler) ->
  {ReplyBin, OpaqueCtx} = do_handle(Body, Handler, ?WITHOUT_OPAQUE, fun lists:mapfoldl/3),
  opaque_on_demand(ReplyBin, OpaqueCtx).

-spec handle(Body :: handle_body(), Handler :: handler_with_opaque(), Opaque :: opaque()) -> {reply, Reply :: iodata(), opaque()} | {noreply, opaque()}.
handle(Body, Handler, Opaque) ->
  {ReplyBin, OpaqueCtx} = do_handle(Body, Handler, ?OPAQUE_CTX(Opaque), fun lists:mapfoldl/3),
  opaque_on_demand(ReplyBin, OpaqueCtx).

-spec handle(Body :: handle_body(), Handler :: handler_with_opaque(), Opaque :: opaque(), MapFoldlFun :: map_handler()) -> {reply, Reply :: iodata(), opaque()} | {noreply, opaque()}.
handle(Body, Handler, Opaque, MapFoldlFun) when is_function(MapFoldlFun, 3) ->
  {ReplyBin, OpaqueCtx} = do_handle(Body, Handler, ?OPAQUE_CTX(Opaque), MapFoldlFun),
  opaque_on_demand(ReplyBin, OpaqueCtx).


-spec handle_term(Term :: handle_term(), Handler :: handler()) -> {reply, Reply :: json:encode_value()} | noreply.
handle_term(Term, Handler) ->
  {ReplyTerm, OpaqueCtx} = do_handle_term(Term, Handler, ?WITHOUT_OPAQUE, fun lists:mapfoldl/3),
  opaque_on_demand(ReplyTerm, OpaqueCtx).

-spec handle_term(Term :: handle_term(), Handler :: handler_with_opaque(), Opaque :: opaque()) -> {reply, Reply :: json:encode_value(), opaque()} | {noreply, opaque()}.
handle_term(Term, Handler, Opaque) ->
  {ReplyTerm, OpaqueCtx} = do_handle_term(Term, Handler, ?OPAQUE_CTX(Opaque), fun lists:mapfoldl/3),
  opaque_on_demand(ReplyTerm, OpaqueCtx).

-spec handle_term(Term :: handle_term(), Handler :: handler_with_opaque(), Opaque :: opaque(), MapFoldlFun :: map_handler()) -> {reply, Reply :: json:encode_value(), opaque()} | {noreply, opaque()}.
handle_term(Term, Handler, Opaque, MapFoldlFun) when is_function(MapFoldlFun, 3) ->
  {ReplyTerm, OpaqueCtx} = do_handle_term(Term, Handler, ?OPAQUE_CTX(Opaque), MapFoldlFun),
  opaque_on_demand(ReplyTerm, OpaqueCtx).


%%% Private

do_handle(Body, Handler, OpaqueCtxIn, MapFoldFun) ->
  {ReplyTerm, OpaqueCtxOut} = try ?DECODE(Body) of
    Term ->
      do_handle_term(Term, Handler, OpaqueCtxIn, MapFoldFun)
  catch Class1:Reason1 ->
    ?LOG_WARNING("Failed to decode request in JSON format: ~tp ~tp", [Class1, Reason1]),
    {response(#{error => parse_error}), OpaqueCtxIn}
  end,

  Reply = case ReplyTerm of
    noreply ->
      noreply;

    _ ->
      try ?ENCODE(ReplyTerm)
      catch Class2:Reason2 ->
        ?LOG_ERROR("Failed to encode response in JSON format: ~tp ~tp", [Class2, Reason2]),
        ?ENCODE(response(#{error => internal_error }))
      end
  end,
  {Reply, OpaqueCtxOut}.


do_handle_term(Term, Handler, OpaqueCtxIn, MapFoldFun) ->
  case parse(Term) of
    [_|_] = Objectives ->
      {Executed, OpaqueCtxOut} = execute(Objectives, Handler, OpaqueCtxIn, MapFoldFun),
      Responses = [R || R <- [ response(E) || E <- Executed], R =/= noreply ],
      case Responses of
        [] -> {noreply, OpaqueCtxOut};
        _ -> {Responses, OpaqueCtxOut}
      end;
    Objective ->
      {[Executed], OpaqueCtxOut} = execute([Objective], Handler, OpaqueCtxIn, MapFoldFun),
      {response(Executed), OpaqueCtxOut}
  end.


opaque_on_demand(noreply, ?OPAQUE_CTX(Opaque)) -> {noreply, Opaque};
opaque_on_demand(noreply, ?WITHOUT_OPAQUE)     -> noreply;
opaque_on_demand(Reply,   ?OPAQUE_CTX(Opaque)) -> {reply, Reply, Opaque};
opaque_on_demand(Reply,   ?WITHOUT_OPAQUE)     -> {reply, Reply}.


response(#{ type := notification}) ->
  noreply;
response(#{ error := Error} = E) ->
  with_header(#{id => maps:get(id, E, null), error => response_error(Error)});
response(#{ result := Result, id := Id}) ->
  with_header(#{id => Id, result => Result}).


response_error({Code, Reason, Data}) when is_integer(Code) andalso (Code < -32768 orelse Code > -32000) -> #{
  code => Code,
  message => response_error_message(Reason),
  data => Data
};
response_error({Code, Reason}) when is_integer(Code) andalso (Code < -32768 orelse Code > -32000) -> #{
  code => Code,
  message => response_error_message(Reason)
};
response_error({Reason, Data}) when is_atom(Reason) ->
  (response_error_tag(Reason))#{
    data => Data
  };
response_error(Reason) when is_atom(Reason) ->
  response_error_tag(Reason).


response_error_tag(parse_error)       -> #{code => -32700, message => ~"Parse error."};
response_error_tag(invalid_request)   -> #{code => -32600, message => ~"Invalid Request."};
response_error_tag(method_not_found)  -> #{code => -32601, message => ~"Method not found."};
response_error_tag(invalid_params)    -> #{code => -32602, message => ~"Invalid params."};
response_error_tag(internal_error)    -> #{code => -32603, message => ~"Internal error."};
response_error_tag(server_error)      -> #{code => -32000, message => ~"Server error."};
response_error_tag(A) when is_atom(A) -> #{
  code => erlang:crc32(atom_to_binary(A)),
  message => response_error_message(A)
}.

response_error_message(A) when is_atom(A) ->
  <<_:8, _/binary>> = B = atom_to_binary(A),
  <<(string:titlecase(binary:replace(B, ~"_", ~" ")))/binary, $.>>;
response_error_message(B) when is_binary(B) -> B.


with_header(#{} = E) ->
  E#{jsonrpc => ~"2.0"}.


parse(Req) when is_map(Req) ->
  Funs = [
    fun parse_version/2,
    fun parse_id/2,
    fun parse_method/2,
    fun parse_params/2,
    fun(_, Obj) -> inspect_type(Obj) end
  ],
  ApplyFun = fun
    (_, Objective = #{error := _}) -> Objective;
    (F, RespAcc) -> F(Req, RespAcc)
  end,
  _Resp = lists:foldl(ApplyFun, #{}, Funs);
parse(Reqs = [_|_]) ->
  [ parse(Req) || Req <- Reqs ];
parse(_) ->
  #{error => invalid_request}.


parse_version(#{<<"jsonrpc">> := <<"2.0">> = V}, Objective) -> Objective#{version => V};
parse_version(_, Objective)                                 -> Objective#{error => invalid_request}.


parse_id(#{<<"id">> := Id = null}, Objective)               -> Objective#{id => Id};
parse_id(#{<<"id">> := Id = <<_:8, _/binary>>}, Objective)  -> Objective#{id => Id};
parse_id(#{<<"id">> := Id}, Objective) when is_integer(Id)  -> Objective#{id => Id};
parse_id(#{<<"id">> := _}, Objective)                       -> Objective#{error => invalid_request};
parse_id(#{ }, Objective)                                   -> Objective;
parse_id(_, Objective)                                      -> Objective#{error => invalid_request}.


parse_method(#{<<"method">> := <<_:8, _/binary>> = Method}, Objective) ->
  Objective#{method => Method};
parse_method(_, Objective) ->
  Objective#{error => invalid_request}.


parse_params(#{<<"params">> := Params}, Objective)  when is_list(Params); is_map(Params) ->
  Objective#{params => Params};
parse_params(#{<<"params">> := _}, Objective) ->
  Objective#{error => invalid_request};
parse_params(#{}, Objective) ->
  Objective#{params => []}.


inspect_type(#{id := _} = Objective) ->
  Objective#{type => request};
inspect_type(#{} = Objective) ->
  Objective#{type => notification}.


execute(Objectives, Handler, ?WITHOUT_OPAQUE, MapFoldFun) ->
  MapFoldFun(fun
    (#{ error := _} = ObjA, _) ->
      {ObjA, ?WITHOUT_OPAQUE};
    (ObjA, _) ->
      Arity = method_arity(ObjA),
      case inspect_handler(ObjA, Handler, Arity) of
        #{ error := _} = ObjB ->
          {ObjB, ?WITHOUT_OPAQUE};
        ObjB ->
          {_, _} = dispatch(ObjB, ?WITHOUT_OPAQUE)
      end
  end, ?WITHOUT_OPAQUE, Objectives);

execute(Objectives, Handler, ?OPAQUE_CTX(Opaque), MapFoldFun) ->
  {Res, ResOpaque} = MapFoldFun(fun
    (#{ error := _} = ObjA, OpaqueIn) -> % errors also go through MapFoldFun for possible request counting
      {ObjA, OpaqueIn};
    (ObjA, OpaqueIn) ->
      Arity = method_arity(ObjA) + 1,
      case inspect_handler(ObjA, Handler, Arity) of % inside MapFioldFun for possible dynamic module loading
        #{ error := _} = ObjB ->
          {ObjB, OpaqueIn};
        ObjB ->
          {ObjC, ?OPAQUE_CTX(OpaqueOut)} = dispatch(ObjB, ?OPAQUE_CTX(OpaqueIn)),
          {ObjC, OpaqueOut}
      end
  end, Opaque, Objectives),
  {Res, ?OPAQUE_CTX(ResOpaque)}.


dispatch(Objective, ?OPAQUE_CTX(OpaqueIn)) ->
  Result = case Objective of
    #{module := Mod, function_name := F, params := #{} = P} -> Mod:F(P, OpaqueIn);
    #{module := Mod, function_name := F, params := P}       -> erlang:apply(Mod, F, P ++ [OpaqueIn]);
    #{method := Method, function := Fun, params := P}       -> Fun(Method, P, OpaqueIn)
  end,
  #{type := Type} = ObjectiveOut = maps:without([params], Objective),
  case {Type, Result} of
    {request, {ok, Ret, OpaqueOut}} -> {ObjectiveOut#{result => Ret}, ?OPAQUE_CTX(OpaqueOut)};
    {request, {ok, Ret}}            -> {ObjectiveOut#{result => Ret}, ?OPAQUE_CTX(OpaqueIn)};
    {notification, {ok, OpaqueOut}} -> {ObjectiveOut, ?OPAQUE_CTX(OpaqueOut)};
    {notification, _}               -> {ObjectiveOut, ?OPAQUE_CTX(OpaqueIn)};
    {_, {error, Reason, OpaqueOut}} -> {ObjectiveOut#{error => Reason}, ?OPAQUE_CTX(OpaqueOut)};
    {_, {error, Reason}}            -> {ObjectiveOut#{error => Reason}, ?OPAQUE_CTX(OpaqueIn)}
  end;

dispatch(Objective, ?WITHOUT_OPAQUE) ->
  Result = case Objective of
    #{module := Mod, function_name := F, params := #{} = P} -> Mod:F(P);
    #{module := Mod, function_name := F, params := P}       -> erlang:apply(Mod, F, P);
    #{method := Method, function := Fun, params := P}       -> Fun(Method, P)
  end,
  #{type := Type} = ObjectiveOut = maps:without([params], Objective),

  case {Type, Result} of
    {request, {ok, Ret}}            -> {ObjectiveOut#{result => Ret}, ?WITHOUT_OPAQUE};
    {notification, _}               -> {ObjectiveOut, ?WITHOUT_OPAQUE};
    {_, {error, Reason}}            -> {ObjectiveOut#{error => Reason}, ?WITHOUT_OPAQUE}
  end.


inspect_handler(Objective, HandlerFun, _Arity) when is_function(HandlerFun, 3) orelse is_function(HandlerFun, 2) ->
  Objective#{ function => HandlerFun };

inspect_handler(Objective = #{ method := M}, HandlerModule, Arity) when is_atom(HandlerModule) ->
  maybe
    {ok, FunctionName} ?= catch {ok, binary_to_existing_atom(M)},
    true ?= erlang:function_exported(HandlerModule, FunctionName, Arity),
    Objective#{ module => HandlerModule, function_name => FunctionName }
  else
    _ -> Objective#{ error => method_not_found }
  end;

inspect_handler(Objective = #{ method := M}, HandlerAllowedModules, Arity) when is_map(HandlerAllowedModules) ->
  maybe
    [ModuleBin, MethodBin] ?= binary:split(M, ?MF_SEP),
    #{ModuleBin := HandlerModule} ?= HandlerAllowedModules,
    {ok, FunctionName} ?= catch {ok, binary_to_existing_atom(MethodBin)},
    true ?= erlang:function_exported(HandlerModule, FunctionName, Arity),
    Objective#{ module => HandlerModule, function_name => FunctionName }
  else
    _ -> Objective#{ error => method_not_found }
  end.


method_arity(#{ params := #{} }) -> 1;
method_arity(#{ params := []  }) -> 0;
method_arity(#{ params := [_|_] = P }) -> length(P).


%%------------
%% Unit tests
%%------------


-ifdef(TEST).
-include_lib("eunit/include/eunit.hrl").
-compile(export_all).

test_make_object(Id)                 -> #{<<"jsonrpc">> => <<"2.0">>, <<"id">> => Id}.
test_make_object(Id, Method)         -> (test_make_object(Id))#{<<"method">> => Method}.
test_make_object(Id, Method, Params) -> (test_make_object(Id, Method))#{<<"params">> => Params}.

'parse/1_positive_test'() ->
  ?assertEqual(#{type => request, id => 567,version => <<"2.0">>, params => [], method => <<"X">>},
    jsonrpc2:parse(test_make_object(567, <<88>>, []))),
  ?assertEqual(#{type => request, id => -10567,version => <<"2.0">>, params=>#{a=>null, b=>true}, method => <<"mod:fun">>},
    jsonrpc2:parse(test_make_object(-10567, <<"mod:fun">>, #{a=>null, b=>true}))),
  ?assertEqual(#{type => request, id => null, version => <<"2.0">>, params => [], method => <<"Y">>},
    jsonrpc2:parse(test_make_object(null, <<89>>, []))).

'parse/1_negative_test'() ->
  ?assertEqual(#{error => invalid_request},
    jsonrpc2:parse(#{})),
  ?assertEqual(#{error => invalid_request},
    jsonrpc2:parse([])),
  ?assertEqual(#{error => invalid_request},
    jsonrpc2:parse(<<>>)),
  ?assertEqual(#{error => invalid_request},
    jsonrpc2:parse(#{<<"jsonrpc">> => <<"2.00">>})),
  ?assertEqual(#{error => invalid_request,version => <<"2.0">>},
    jsonrpc2:parse(#{<<"jsonrpc">> => <<"2.0">>})),
  ?assertEqual(#{error => invalid_request,id => <<"x-m">>,version => <<"2.0">>},
    jsonrpc2:parse(test_make_object(<<"x-m">>))),
  ?assertEqual(#{error => invalid_request, id => -10568, version => <<"2.0">>},
    jsonrpc2:parse(test_make_object(-10568, undefined, #{a=>null, b=>true}))),
  ?assertEqual(#{error => invalid_request,version => <<"2.0">>},
    jsonrpc2:parse(test_make_object(undefined, <<87>>, []))),
  ?assertEqual(#{error => invalid_request, version => <<"2.0">>},
    jsonrpc2:parse(test_make_object(#{}))).



test_handler(M, A, O) ->
  case test_handler(M, A) of
    ok -> {ok, O + 1};
    T -> list_to_tuple(tuple_to_list(T)  ++ [O + 1])
  end.

test_handler(<<"subtract">>, [A, B]) -> {ok, A - B};
test_handler(<<"subtract">>, #{<<"subtrahend">> := 23, <<"minuend">> := 42}) -> {ok, 19};
test_handler(<<"update">>, [1, 2, 3, 4, 5]) -> ok;
test_handler(<<"sum">>, [1, 2, 4]) -> {ok, 7};
test_handler(<<"get_data">>, []) -> {ok, [<<"hello">>, 5]};
test_handler(_, _) -> {error, method_not_found}.


test_handler_module_subtract(A, B) -> {ok, A - B}.
test_handler_module_subtract(A, B, C) -> {ok, A - B - C}.

test_handler_module_subtract_opaque(A, B, O) -> {ok, A - B, O + 1}.
test_handler_module_subtract_opaque(A, B, C, O) -> {ok, A - B - C, O + 1}.

test_handler_module_notify() -> any_term.
test_handler_module_notify_opaque(O) -> {ok, O + 1}.


-define(OBJ(M), maps:merge(#{jsonrpc => ~"2.0"}, M)).
-define(BIN(M),  iolist_to_binary(json:encode(M))).
-define(TERM(M),  json:decode(?BIN(M))).
-define(DECODE_REPLY(R), json:decode(iolist_to_binary(R))).

-define(REQUEST_TERMS, [ ?TERM(?OBJ(#{id => -N, method => subtract, params => [N+11, 11]})) || N <- lists:seq(10, 20) ]).
-define(EXPECTED_TERMS, [ ?OBJ(#{id => -N, result => N}) || N <- lists:seq(10, 20) ]).

'handle_term/2_test'() ->
  Result = handle_term(hd(?REQUEST_TERMS), fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(hd(?EXPECTED_TERMS), element(2, Result)).

'handle_term/2_batch_test'() ->
  [ begin
      Result = handle_term(lists:sublist(?REQUEST_TERMS, C), fun test_handler/2),
      ?assertMatch({reply, _}, Result),
      ?assertEqual(lists:sublist(?EXPECTED_TERMS, C), element(2, Result))
    end || C <- lists:seq(1, length(?REQUEST_TERMS)) ].

'handle_raw_/3_test'() ->
  Opaque = 1001,
  Result = handle_term(hd(?REQUEST_TERMS), fun test_handler/3, Opaque),
  ?assertMatch({reply, _, _}, Result),
  ?assertEqual(hd(?EXPECTED_TERMS), element(2, Result)),
  ?assertEqual(Opaque + 1, element(3, Result)).

'handle_term/3_batch_test'() ->
  Opaque = 1001,
  [ begin
      Result = handle_term(lists:sublist(?REQUEST_TERMS, C), fun test_handler/3, Opaque),
      ?assertMatch({reply, _, _}, Result),
      ?assertEqual(lists:sublist(?EXPECTED_TERMS, C), element(2, Result)),
      ?assertEqual(Opaque + C, element(3, Result))
    end || C <- lists:seq(1, length(?REQUEST_TERMS)) ].

'handle/2_test'() ->
  Result = handle(?BIN(hd(?REQUEST_TERMS)), fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(hd(?EXPECTED_TERMS)), ?DECODE_REPLY(element(2, Result))).

'handle/2_batch_test'() ->
  [ begin
      Result = handle(?BIN(lists:sublist(?REQUEST_TERMS, C)), fun test_handler/2),
      ?assertMatch({reply, _}, Result),
      ?assertEqual(?TERM(lists:sublist(?EXPECTED_TERMS, C)), ?DECODE_REPLY(element(2, Result)))
    end || C <- lists:seq(1, length(?REQUEST_TERMS)) ].


'handle/3_test'() ->
  Opaque = 1001,
  Result = handle(?BIN(hd(?REQUEST_TERMS)), fun test_handler/3, Opaque),
  ?assertMatch({reply, _, _}, Result),
  ?assertEqual(?TERM(hd(?EXPECTED_TERMS)), ?DECODE_REPLY(element(2, Result))),
  ?assertEqual(Opaque + 1, element(3, Result)).

'handle/3_batch_test'() ->
  Opaque = 1001,
  [ begin
      Result = handle(?BIN(lists:sublist(?REQUEST_TERMS, C)), fun test_handler/3, Opaque),
      ?assertMatch({reply, _, _}, Result),
      ?assertEqual(?TERM(lists:sublist(?EXPECTED_TERMS, C)), ?DECODE_REPLY(element(2, Result))),
      ?assertEqual(Opaque + C, element(3, Result))
    end || C <- lists:seq(1, length(?REQUEST_TERMS)) ].


'handle/2_notify_test'() ->
  Notify = ?OBJ(#{method => update, params => [1, 2, 3, 4, 5]}),
  ?assertEqual(noreply, handle(?BIN(Notify), fun test_handler/2)),
  ?assertEqual(noreply, handle(?BIN([Notify]), fun test_handler/2)),
  ?assertEqual(noreply, handle(?BIN([Notify, Notify]), fun test_handler/2)),

  Request = ?OBJ(#{method => sum, params => [1, 2, 4], id => 99}),
  Result = handle(?BIN([Notify, Request,Notify]), fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM([?OBJ(#{id => 99, result => 7})]), ?DECODE_REPLY(element(2, Result))).


'handle/3_notify_test'() ->
  Opaque = 1001,
  Notify = ?OBJ(#{method => update, params => [1, 2, 3, 4, 5]}),
  ?assertEqual({noreply, 1002}, handle(?BIN(Notify), fun test_handler/3, Opaque)),
  ?assertEqual({noreply, 1002}, handle(?BIN([Notify]), fun test_handler/3, Opaque)),
  ?assertEqual({noreply, 1003}, handle(?BIN([Notify, Notify]), fun test_handler/3, Opaque)),

  Request = ?OBJ(#{method => sum, params => [1, 2, 4], id => -99}),
  Result = handle(?BIN([Notify, Request,Notify]), fun test_handler/3, Opaque),
  ?assertMatch({reply, _, _}, Result),
  ?assertEqual(?TERM([?OBJ(#{id => -99, result => 7})]), ?DECODE_REPLY(element(2, Result))),
  ?assertEqual(Opaque + 3, element(3, Result)).

'handle/2_module_test'() ->
  Request  = ?OBJ(#{id => 76, method => test_handler_module_subtract, params => [-11, 20]}),
  Expected = ?OBJ(#{id => 76, result => -31}),
  Result   = handle(?BIN(Request), ?MODULE),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

'handle/3_module_test'() ->
  Opaque   = 1001,
  Request  = ?OBJ(#{id => 77, method => test_handler_module_subtract_opaque, params => [-11, 20]}),
  Expected = ?OBJ(#{id => 77, result => -31}),
  Result   = handle(?BIN(Request), ?MODULE, Opaque),
  ?assertMatch({reply, _,_}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))),
  ?assertEqual(Opaque + 1, element(3, Result)).

'handle/2_allowed_modules_test'() ->
  Method1 = ~"FUN_SCOPE_1:test_handler_module_subtract",
  Method2 = ~"FUN_SCOPE_2:test_handler_module_subtract",
  MethodNotFound1 = ~"FUN_SCOPE_NOT_FOUND:test_handler_module_subtract",
  MethodNotFound2 = ~"FUN_SCOPE_1:test_handler_module_subtract_NOT_FOUND",
  AllowedOverrides = #{~"FUN_SCOPE_1" => ?MODULE, ~"FUN_SCOPE_2" => ?MODULE},

  Request = [
    ?OBJ(#{id => 78, method => Method1, params => [-11, 21]}),
    ?OBJ(#{id => 79, method => Method2, params => [-11, 22]}),
    ?OBJ(#{id => 80, method => MethodNotFound1, params => [0, 0]}),
    ?OBJ(#{id => 81, method => MethodNotFound2, params => [0, 0]})
  ],

  Expected = [
    ?OBJ(#{id => 78, result => -32}),
    ?OBJ(#{id => 79, result => -33}),
    ?OBJ(#{id => 80, error => #{code => -32601, message => ~"Method not found."}}),
    ?OBJ(#{id => 81, error => #{code => -32601, message => ~"Method not found."}})
  ],
  Result = handle(?BIN(Request), AllowedOverrides),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

'handle/3_allowed_modules_test'() ->
  Method1 = ~"FUN_SCOPE_1:test_handler_module_subtract_opaque",
  Method2 = ~"FUN_SCOPE_2:test_handler_module_subtract_opaque",
  MethodNotFound1 = ~"FUN_SCOPE_NOT_FOUND:test_handler_module_subtract_opaque",
  MethodNotFound2 = ~"FUN_SCOPE_1:test_handler_module_subtract_opaque_NOT_FOUND",
  AllowedOverrides = #{~"FUN_SCOPE_1" => ?MODULE, ~"FUN_SCOPE_2" => ?MODULE},

  Opaque = 1001,
  Request = [
    ?OBJ(#{id => 82, method => Method1, params => [-11, 21]}),
    ?OBJ(#{id => 83, method => Method2, params => [-11, 22]}),
    ?OBJ(#{id => 84, method => MethodNotFound1, params => [0, 0]}),
    ?OBJ(#{id => 85, method => MethodNotFound2, params => [0, 0]})
  ],

  Expected = [
    ?OBJ(#{id => 82, result => -32}),
    ?OBJ(#{id => 83, result => -33}),
    ?OBJ(#{id => 84, error => #{code => -32601, message => ~"Method not found."}}),
    ?OBJ(#{id => 85, error => #{code => -32601, message => ~"Method not found."}})
  ],
  Result = handle(?BIN(Request), AllowedOverrides, Opaque),
  ?assertMatch({reply, _, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))),
  ?assertEqual(Opaque + 2, element(3, Result)).

% TODO: handle/4 tests


%% Testing the examples from http://www.jsonrpc.org/specification

%% rpc call with positional parameters
call_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "subtract", "params": [42, 23], "id": 1}',
  Expected   = ?OBJ(#{id => 1, result => 19}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with positional parameters, reverse order
call2_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "subtract", "params": [23, 42], "id": 2}',
  Expected   = ?OBJ(#{id => 2, result => -19}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with named parameters
named_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "subtract", "params": {"subtrahend": 23, "minuend": 42}, "id": 3}',
  Expected   = ?OBJ(#{id => 3, result => 19}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with named parameters, reverse order
named2_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "subtract", "params": {"minuend": 42, "subtrahend": 23}, "id": 4}',
  Expected   = ?OBJ(#{id => 4, result => 19}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% a Notification
notif_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "update", "params": [1,2,3,4,5]}',
  ?assertEqual(noreply, handle(RequestBin, fun test_handler/2)).

%% a Notification + non-existent method
notif2_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "foobar"}',
  ?assertEqual(noreply, handle(RequestBin, fun test_handler/2)).

%% rpc call of non-existent method
bad_method_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "foobar", "id": "1"}',
  Expected   = ?OBJ(#{id => ~"1", error => #{code => -32601, message => ~"Method not found."}}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with invalid JSON
bad_json_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": "foobar, "params": "bar", "baz]',
  Expected   = ?OBJ(#{error => #{code => -32700, message => ~"Parse error."}, id => null}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with invalid Request object
bad_rpc_test() ->
  RequestBin = ~'{"jsonrpc": "2.0", "method": 1, "params": "bar"}',
  Expected   = ?OBJ(#{error => #{code => -32600, message => ~"Invalid Request."}, id => null}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call Batch, invalid JSON:
bad_json_batch_test() ->
  RequestBin = ~'[{"jsonrpc": "2.0", "method": "sum", "params": [1,2,4], "id": "1"},{"jsonrpc": "2.0", "method"]',
  Expected   = ?OBJ(#{error => #{code => -32700, message => ~"Parse error."}, id => null}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with an empty Array
empty_batch_test() ->
  RequestBin = ~"[]",
  Expected   = ?OBJ(#{error => #{code => -32600, message => ~"Invalid Request."}, id => null}),
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with an invalid Batch (but not empty)
invalid_batch_test() ->
  RequestBin = ~"[1]",
  Expected   = [?OBJ(#{error => #{code => -32600, message => ~"Invalid Request."}, id => null})],
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call with invalid Batch
invalid_batch2_test() ->
  RequestBin = ~"[1,2,3]",
  Resp       = ?OBJ(#{error => #{code => -32600, message => ~"Invalid Request."}, id => null}),
  Expected   = [Resp, Resp, Resp],
  Result     = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call Batch
batch_test() ->
  RequestBin = ~'[
    {"jsonrpc": "2.0", "method": "sum", "params": [1,2,4], "id": "1"},
    {"jsonrpc": "2.0", "method": "notify_hello", "params": [7]},
    {"jsonrpc": "2.0", "method": "subtract", "params": [42,23], "id": "2"},
    {"foo": "boo"},
    {"jsonrpc": "2.0", "method": "foo.get", "params": {"name": "myself"}, "id": "5"},
    {"jsonrpc": "2.0", "method": "get_data", "id": "9"} 
  ]',
  Expected = [
    ?OBJ(#{id => ~"1", result => 7}),
    ?OBJ(#{id => ~"2", result => 19}),
    ?OBJ(#{error => #{code => -32600, message => ~"Invalid Request."}, id => null}),
    ?OBJ(#{error => #{code => -32601, message => ~"Method not found."}, id => ~"5"}),
    ?OBJ(#{id => ~"9", result => [hello, 5]})
  ],
  Result = handle(RequestBin, fun test_handler/2),
  ?assertMatch({reply, _}, Result),
  ?assertEqual(?TERM(Expected), ?DECODE_REPLY(element(2, Result))).

%% rpc call Batch (all notifications)
batch_notif_test() ->
  RequestBin = ~'[
    {"jsonrpc": "2.0", "method": "notify_sum", "params": [1,2,4]},
    {"jsonrpc": "2.0", "method": "notify_hello", "params": [7]}
  ]',
  ?assertEqual(noreply, handle(RequestBin, fun test_handler/2)).

response_error_test() ->
  ?assertEqual(#{code => -32769, message => <<>>, data => #{a => b}}, response_error({-32769, <<>>, #{a => b}})),
  ?assertEqual(#{code => -31999, message => ~"a", data => #{a => b}}, response_error({-31999, ~"a", #{a => b}})),
  ?assertError(function_clause, response_error({-32768, <<>>, #{}})),
  ?assertError(function_clause, response_error({-32000, <<>>, #{}})),

  ?assertEqual(#{code => -32769, message => <<>>}, response_error({-32769, <<>>})),
  ?assertEqual(#{code => -31999, message => ~"a"}, response_error({-31999, ~"a"})),
  ?assertError(function_clause, response_error({-32768, <<>>})),
  ?assertError(function_clause, response_error({-32000, <<>>})),

  Data = #{
    parse_error       => #{code => -32700, message => ~"Parse error."},
    invalid_request   => #{code => -32600, message => ~"Invalid Request."},
    method_not_found  => #{code => -32601, message => ~"Method not found."},
    invalid_params    => #{code => -32602, message => ~"Invalid params."},
    internal_error    => #{code => -32603, message => ~"Internal error."},
    server_error      => #{code => -32000, message => ~"Server error."}
  },

  [ begin
    X = #{rand:uniform(1000) => rand:uniform(1000)},
    ?assertEqual(Expected#{data => X}, response_error({Reason, X})),
    ?assertEqual(Expected, response_error(Reason))
  end || Reason := Expected <- Data ],

  ?assertEqual(#{code => 2732708230, message => ~"User defined."}, response_error(user_defined)),
  ?assertEqual(#{code => 629900081, message => ~"User defined for Great Good."}, response_error('user defined for Great Good')).


-endif.
