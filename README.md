JSON-RPC 2.0 for Erlang
=======================

Library for JSON-RPC 2.0 using JSON library (EEP 68) from stdlib, logger (OTP 21.0) and Maps (EEP 43).


Dependencies
------------

* Erlang/OTP 27.0+


Features
--------

* transport neutral;
* dispatches parsed requests to a simple callback function;
* supports an optional callback "map" function for batch requests, e.g. to
  support concurrent processing of the requests in a batch or collecting statistics;
* handles rpc calls and notifications;
* supports named and unnamed parameters;
* includes unit tests for all examples in the JSON-RPC 2.0 specification.

Server examples
-------

```erlang
1> Body = ~'{"jsonrpc": "2.0", "method": "foo", "params": [1,2,3], "id": 1}'.
<<"{\"jsonrpc\": \"2.0\", \"method\": \"foo\", \"params\": [1,2,3], \"id\": 1}">>

2> Handler = fun(~"foo", Params) -> {ok, lists:reverse(Params)}; (_, _) -> {error, method_not_found} end.
#Fun<erl_eval.41.81571850>

3> jsonrpc2:handle(Body, Handler).
{reply,["{",
        [[34,<<"id">>,34],58|<<"1">>],
        [[44,
          [34,<<"result">>,34],
          58,91,<<"3">>,44,<<"2">>,44,<<"1">>,93],
         [44,[34,<<"jsonrpc">>,34],58,34,<<"2.0">>,34]],
        "}"]}

4> jsonrpc2:handle(~"dummy", Handler).
=WARNING REPORT==== 10-Aug-2025::13:58:12.336132 ===
Failed to decode request in JSON format: error {invalid_byte,100}
{reply,["{",
        [[34,<<"error">>,34],
         58,"{",
         [[34,<<"code">>,34],58|<<"-32700">>],
         [[44,[34,<<"message">>,34],58,34,<<"Parse error.">>,34]],
         "}"],
        [[44,[34,<<"id">>,34],58|<<"null">>],
         [44,[34,<<"jsonrpc">>,34],58,34,<<"2.0">>,34]],
        "}"]}

5> {reply, R} = jsonrpc2:handle(~'{"x": 42}', Handler).
{reply,["{",
        [[34,<<"error">>,34],
         58,"{",
         [[34,<<"code">>,34],58|<<"-32600">>],
         [[44,[34,<<"message">>,34],58,34,<<"Invalid Request.">>,34]],
         "}"],
        [[44,[34,<<"id">>,34],58|<<"null">>],
         [44,[34,<<"jsonrpc">>,34],58,34,<<"2.0">>,34]],
        "}"]}

6> iolist_to_binary(R).
<<"{\"error\":{\"code\":-32600,\"message\":\"Invalid Request.\"},\"id\":null,\"jsonrpc\":\"2.0\"}">>


7> Term = #{~"jsonrpc" => ~"2.0", ~"method" => ~"foo", ~"params" => [1,2,3], ~"id" => 1}.
#{<<"id">> => 1,<<"jsonrpc">> => <<"2.0">>,
  <<"method">> => <<"foo">>,
  <<"params">> => [1,2,3]}

8> jsonrpc2:handle_term(Term, Handler).
{reply,#{id => 1,result => [3,2,1],jsonrpc => <<"2.0">>}}

```


Client example
--------------


```erlang
1> RequestsSpec = [
        #{method => add, params => [7000, -77]},
        #{method => add, params => [-1, 900], id => 0}
    ].
[#{params => [7000,-77],method => add},
 #{id => 0,params => [-1,900],method => add}]

2> TransportFn = fun(Body) -> {ok, {_,_,Resp}} = httpc:request(post, {"http://localhost:8080/rpc", [{"Content-Length", integer_to_binary(iolist_size(Body))}], "application/json", Body}, [], [{body_format, binary}]), Resp end.
#Fun<erl_eval.42.81571850>

jsonrpc2_client:multi_call(RequestsSpec, TransportFn, 1).
[{ok,899,undefined}]

```


Links
-----

* The JSON-RPC 2.0 specification, http://www.jsonrpc.org/specification
* rjsonrpc2, a "restricted" implementation of JSON-RPC 2.0, https://github.com/imprest/rjsonrpc2
* ejrpc2, another JSON-RPC 2 library, https://github.com/jvliwanag/ejrpc2


License
-------

```
Copyright 2013-2014 Viktor Söderqvist
Copyright 2025 Andy (https://github.com/m-2k)

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

   http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
```
