:- module(_, [], [assertions, fsyntax, datafacts, dcg, hiord]).

%! \title Ciao SMT solver interface
%! \author Jose F. Morales
%
%  \module This module provides a generic SMT solver interface for
%  Ciao based on SMT-LIB.

:- use_module(engine(attributes)).

% ---------------------------------------------------------------------------
%! # Solver flags

:- data solver_opt/2.

:- export(set_solver_opt/2).
set_solver_opt(Opt, Val) :-
    retractall_fact(solver_opt(Opt, _)),
    assertz_fact(solver_opt(Opt, Val)).

:- export(get_solver_opt/2).
get_solver_opt(Opt, Val) :-
    ( solver_opt(Opt, Val0) -> Val = Val0
    ; fail
    ).

% ---------------------------------------------------------------------------

:- data fun_sorts/3.
:- data fun_def/3.

:- export(reset_defs/0).
:- pred reset_defs # "Erase user definitions (e.g., functions)".
reset_defs :-
    retractall_fact(fun_sorts(_,_,_)),
    retractall_fact(fun_def(_,_,_)).

:- export(assert_fun/2).
:- pred assert_fun(Head,Body) # "Assert a new function with head
   @var{Head} (type-annotated) and body @var{Body}".

assert_fun(X::Ty, Def) :-
    X=..[F|Decls],
    functor(X,F,A),
    functor(X2,F,A),
    Ats = ~decls_ty(Decls),
    assertz_fact(fun_sorts(X2, Ats, Ty)),
    assertz_fact(fun_def(X, Ty, Def)).

decls_ty([]) := [].
decls_ty([(_::Ty)|Decls]) := [Ty|Tys] :-
    Tys = ~decls_ty(Decls).

% ---------------------------------------------------------------------------
%! # SMT formulae

% TODO: make it generic?
% Box a value (merges value and type), keep unchanged underwise % TODO: unbox (extracts type from value)
box(bitvec(Xw),X) := bv(X,Xw) :- integer(X), !.
box(Ty,X) := X :-
    ( var(X) -> declvar(X, Ty) ; true ).

%:- export(unbox/2).
% TODO: make it generic?
% Unbox representation for some values (drops type)
unbox(X) := X :- var(X), !.
unbox(bv(X,_)) := X :- !,
    ( integer(X) -> true ; throw(bug_wrong_bv(X)) ).
unbox(X) := X.

% NOTE: Dic uses "incomplete" data structures to represent maps with
% symbolic values for keys. Currently keys must be concrete.
%
% Note: while write operations produce different maps for the
%   changed values, reads must propagate new assignments to previous
%   versions. Example:
%
%   ?- 1 = ~eval(select(D,x)), D2 = ~eval(store(D,y,2)), 3 = ~eval(select(D2,a)).
%   
%   D = [x=1,a=3|_A],
%   D2 = [x=1,y=2,a=3|_A] ? 
%
% Note: do not use library(dict) since it does not fulfill the
%   property above. Example:
%
%   % ok
%   ?- dic_lookup(D,x,1), dic_replace(D,y,2,D2), dic_lookup(D2,a,3).
%   D = dic(x,1,dic(a,3,_A,_B),_),
%   D2 = dic(x,1,dic(a,3,_A,_B),dic(y,2,_,_)) ? 
%
%   % wrong
%   ?- dic_lookup(D,x,1), dic_replace(D,y,2,D2), dic_lookup(D2,z,3).
%   D = dic(x,1,_A,_),
%   D2 = dic(x,1,_A,dic(y,2,_,dic(z,3,_,_))) ? 

% TODO: optimize the current O(n) map implementation:
%   - Keep linear and ordered when K is unknown (note that they could even repeat)
%   - Periodically compact into a fixed form (using good structures)

% TODO: introduce as an "alias" in eval/2?
:- export(new_array/4).
% Create an array R of types (Kt,Vt) from key-value (K=V) list
% (KVs). Keys must be concrete.
new_array(Kt, Vt, KVs) := R :-
    ( nonvar(Kt) -> true
    ; throw(error(wrong_key_type, new_array/4))
    ),
    ( nonvar(Vt) -> true
    ; throw(error(wrong_value_type, new_array/4))
    ),
    ( type(R,var) -> true
    ; throw(error(bound_output, new_array/4))
    ),
    Ty=array(Kt,Vt),
    new_array_(KVs, Ys),
    attach_attribute(Tmp, v(Ys,Ty)),
    R = Tmp.

new_array_([], _). % (open)
new_array_([K=V|KVs], [K=V|Dic]) :-
    new_array_(KVs, Dic).

:- export(array_elems/2).
% Obtain key-value (K=V) pairs from the array Dic. Keys must be concrete.
% TODO: introduce as an "alias" in eval/2?
array_elems(Dic) := Xs :-
    ( get_attribute(Dic, v(Ys,Ty)) -> true
    ; throw(error(not_initialized, array_elems/2))
    ),
    ( Ty=array(_Kt,_Vt) -> true % TODO: use Kt,Vt for boxing?
    ; throw(error(not_an_array, array_elems/2))
    ),
    array_elems_(Ys, Xs).

array_elems_(Dic, Xs) :- var(Dic), !, Xs = [].
array_elems_([K=V|Xs0], [K=V|Xs]) :-
    ( nonvar(V), V=bv(_,_) ->
        throw(bug_unboxed_in_map(K,V)) % TODO: not needed now?
    ; true
    ),
    array_elems_(Xs0, Xs).

:- export(is_const_exp/1).
% Expression is a constant
is_const_exp(X) :- var(X), !, fail.
is_const_exp(X) :- integer(X), !.
is_const_exp(X) :- X=bv(_,_), !.

:- export(is_bool_exp/1).
% Expression is a boolean
is_bool_exp(A) :- var(A), !, fail.
is_bool_exp(_=_).
is_bool_exp(_\=_).
is_bool_exp(uge(_,_)).
is_bool_exp(ug(_,_)).
is_bool_exp(ul(_,_)).
is_bool_exp(ule(_,_)).
is_bool_exp(_>=_).
is_bool_exp(_>_).
is_bool_exp(_<_).
is_bool_exp(_=<_).

:- export(assign_eval/2).
% TODO: generalize as 'propagate'?
% Evaluate X and assign its value to a fresh variable To
% (requires concretized X)
assign_eval(To, X) :-
    eval_u(X,Xv,Xt),
    To = ~newsym(Xv,Xt).

% Y is a new symbolic variable with value V
newsym(V,Ty) := Y :-
    Y0 = _,
    attach_attribute(Y0, v(V,Ty)),
    Y = Y0.

:- export(negbool/2).
negbool(X=Y) := (X\=Y).
negbool(X\=Y) := (X=Y).

:- export(declvar/2).
% Declare that variable Var has sort Ty (Var::Ty)
declvar(Var,Ty) :-
    ( get_attribute(Var, v(_,Ty0)) ->
        Ty=Ty0
    ; Var0 = _,
      attach_attribute(Var0, v(_,Ty)),
      Var = Var0
    ).

% % Get type of symbolic variable
% vartype(Var) := Ty :-
%     ( nonvar(Var) ->
%         throw(error(not_a_var, vartype/2))
%     ; get_attribute(Var, v(_,Ty0)) ->
%         Ty=Ty0
%     ; throw(error(missing_type, vartype/2))
%     ).

% ---------------------------------------------------------------------------

:- export(assign_default/1).
% Assign a default value for X (for eval/2)
assign_default(X) :-
    ( get_attribute(X, v(Xv,Xt)) -> true
    ; throw(error(unknown_sort(X), assign_default/1))
    ),
    ( nonvar(Xv) -> true % (already assigned)
    ; ty_default(Xt, Xv)
    ).

% ---------------------------------------------------------------------------

:- export(eval/2).
% eval(X, V): Evaluate the expression X as V (boxed)
%   All relevant variables in X must have concrete values assigned.
eval(X) := V :-
    eval_u(X, R, Ty),
    V = ~box(Ty,R).

% (result is unboxed R-Ty)
eval_u(X, R, Ty) :- var(X), !,
    % assign a default value for X
    ( get_attribute(X, v(Xv,Xt)) -> Ty=Xt
    ; throw(error(unknown_sort(X), eval/3))
    ),
    ( nonvar(Xv) -> true
    ; throw(error(unbound(X), eval/3))
    ),
    R = Xv.
eval_u(N, R, Ty) :- integer(N), !, Ty=int, R=N.
eval_u(true, R, Ty) :- !, Ty=bool, R=1.
eval_u(false, R, Ty) :- !, Ty=bool, R=0.
eval_u(bv(X,Xw), R, Ty) :- !, Ty=bitvec(Xw), R = ~fixwidth(Xw, X).
eval_u(extract(High,Low,A), R, Ty) :- !,
    eval_u(A, Ar, At),
    ( At = bitvec(_) -> true % TODO: check size?
    ; throw(error(expected_bitvector, eval/3))
    ),
    Size is High-Low+1,
    Ty=bitvec(Size),
    R is ((1<<Size)-1)/\(Ar>>Low).
eval_u(X, R, Ty) :- datatype0(X, Ty0, R0), !, Ty=Ty0, R=R0.
%
eval_u(store(Dic, K, V), Dic2, Ty) :- !,
    ( get_attribute(Dic, v(Xs,Ty)) -> true
    ; throw(error(not_array, eval_u/3))
    ),
    ( Ty=array(Kt0,_Vt) -> true % TODO: check that type of V is _Vt
    ; throw(error(not_array, eval_u/3))
    ),
    eval_u(K,Kv,Kt),
    ( Kt0==Kt -> true
    ; throw(error(key_type_mismatch(Kt0,Kt), eval_u/3))
    ),
    % TODO: distinguish between arrays with fully concrete keys and symbolic arrays
    Xs2 = ~eval_store_(Xs,Kv,~unbox(V)),
    attach_attribute(Tmp2, v(Xs2,Ty)),
    Dic2 = Tmp2.
eval_u(select(Dic,K), V0, V0t) :- !,
    eval_select_u(Dic,K,V0,V0t).
%
eval_u(X, R, Ty) :-
    X =.. [F|As],
    eval_us(As, As2, Ats),
    ( f_sorts(X, Ats, Ty0, Vers) ->
        % found sort match
        Ty=Ty0
    ; throw(error(cannot_match_sort(F, Ats), eval/3))
    ),
    X2 =.. [F|As2],
    R = ~f_eval(Vers, X2).

eval_us([], [], []).
eval_us([X|Xs], [X2|Xs2], [Ty|Ts]) :-
    eval_u(X, X2, Ty),
    eval_us(Xs, Xs2, Ts).

eval_store_(Xs,K,V) := [K=V|Xs] :- var(Xs), !.
eval_store_([K0=_|Xs],K,V) := [K=V|Xs] :- K0 == K, !.
eval_store_([K0=V0|Xs],K,V) := [K0=V0| ~eval_store_(Xs,K,V)].

eval_select_u(Dic,K,V,Vt) :-
    ( get_attribute(Dic, v(Xs,Ty)) ->
        Ty=array(Kt,Vt)
    ; throw(error(unknown_sort(Dic), eval_select/3))
    ),
    eval_u(K,Kv,Kt0),
    ( Kt==Kt0 -> true
    ; throw(error(key_type_mismatch(Kt,Kt0), eval_select/3))
    ),
    V = ~eval_select_(Xs,Kv).

eval_select_(Xs,K) := V :- var(Xs), !, Xs=[K=V|_].
eval_select_([K0=V0|_],K) := V :- K0 == K, !, V = V0.
eval_select_([_|Xs],K) := ~eval_select_(Xs,K).

% ---------------------------------------------------------------------------
% TODO: generalize

% TODO: ad-hoc for 'regs' Fixme!
datatype0(X, Ty, R) :-
    atom(X), Ty=regs, R=X.

datatype_ty(regs).

% ---------------------------------------------------------------------------
%! # Theory definitions

% See SMT-LIB theories at http://smtlib.cs.uiowa.edu/theories.shtml

% types
:- discontiguous(ty_smt/2).
%:- discontiguous(ty_smtid/2).
%:- discontiguous(ty_smtdef/2).
:- discontiguous(ty_smtval/3).
:- discontiguous(ty_check/2). % that a value is a primitive value of the given type
:- discontiguous(ty_default/2). % some default value for the type

% expressions
:- discontiguous(f_eval/3). % (assume arguments passed through eval/3)
:- discontiguous(f_sorts/4).
:- discontiguous(f_smt/2). % name for smtlib
:- discontiguous(f_alias/2). % (for renamings)

ty_smt(bitvec(Tw)) := sexp(['_', 'BitVec', Tw]) :- integer(Tw).
%ty_smtid(bitvec(64)) := 'Int64'.
%ty_smtdef(bitvec(64)) := sexp(['_', 'BitVec', 64]).
ty_check(bitvec(_Tw), X) :- integer(X), !.
ty_default(bitvec(_Tw)) := 0.
ty_smtval(bitvec(Tw), X) := bitvecval(X,Tw). % :- integer(Tw).

ty_smt(array(Kt,Vt)) := sexp(['Array', ~ty_smt(Kt), ~ty_smt(Vt)]).
%ty_smtid(array(bitvec(64),bitvec(64))) := 'Array64'.
%ty_smtdef(array(bitvec(64,bitvec(64)))) := sexp(['Array', 'Int64', 'Int64']).

ty_smt(bool) := 'Bool'.

% ---------------------------------------------------------------------------
%! ## Ints
%  http://smtlib.cs.uiowa.edu/theories-Ints.shtml

ty_smt(int) := 'Int'.

f_sorts(+_, [int], int, '+int') :- !.
f_eval('+int', +X) := X :- !.
f_alias(+A) := A.

f_sorts(-_, [int], int, '-int') :- !.
f_eval('-int', -X) := R :- !, R is -X.
f_smt('-int') := '-' :- !.

f_sorts(_+_, [int,int], int, 'int+int') :- !.
f_eval('int+int', X+Y) := R :- !, R is X + Y.
f_smt('int+int') := '+' :- !.

f_sorts(_-_, [int,int], int, 'int-int') :- !.
f_eval('int-int', X-Y) := R :- !, R is X - Y.
f_smt('int-int') := '-' :- !.

f_sorts(_*_, [int,int], int, 'int*int') :- !.
f_eval('int*int', X*Y) := R :- !, R is X * Y.
f_smt('int*int') := '*' :- !.

f_sorts(_>=_, [int,int], bool, 'int>=int') :- !.
f_eval('int>=int', X>=Y) := R :- !, ( X >= Y -> R = 1 ; R = 0 ).
f_smt('int>=int') := '>=' :- !.

f_sorts(_>_, [int,int], bool, 'int>int') :- !.
f_eval('int>int', X>Y) := R :- !, ( X > Y -> R = 1 ; R = 0 ).
f_smt('int>int') := '>' :- !.

f_sorts(_<_, [int,int], bool, 'int<int') :- !.
f_eval('int<int', X<Y) := R :- !, ( X < Y -> R = 1 ; R = 0 ).
f_smt('int<int') := '<' :- !.

f_sorts(_=<_, [int,int], bool, 'int=<int') :- !.
f_eval('int=<int', X=<Y) := R :- !, ( X =< Y -> R = 1 ; R = 0 ).
f_smt('int=<int') := '<=' :- !.

% ---------------------------------------------------------------------------
%! ## Core
%  http://smtlib.cs.uiowa.edu/theories-Core.shtml

f_sorts(not(_), [bool], bool, 'not(bool)') :- !.
f_eval('not(bool)', not(X)) := R :- !, ( X = 1 -> R = 0 ; R = 1 ).
f_smt('not(bool)') := 'not' :- !.

% TODO: use =>?
f_sorts((_->_), [bool,bool], bool, 'bool->bool') :- !.
f_eval('bool->bool', (A->B)) := R :- !, ( A = 1 -> R = B ; R = 0 ).
f_smt('bool->bool') := '=>' :- !.

% TODO: use 'and' or &?
f_sorts((_,_), [bool,bool], bool, 'bool,bool') :- !.
f_eval('bool,bool', (A,B)) := R :- !, R is A/\B.
f_smt('bool,bool') := 'and' :- !.

% TODO: use |?
f_sorts((_;_), [bool,bool], bool, 'bool;bool') :- !.
f_eval('bool;bool', (A;B)) := R :- !, R is A\/B.
f_smt('bool;bool') := 'or' :- !.

% TODO: use #?
f_sorts(xor(_,_), [bool,bool], bool, 'xor(bool,bool)') :- !.
f_eval('xor(bool,bool)', xor(A,B)) := R :- !, R is A # B.
f_smt('xor(bool,bool)') := 'xor' :- !.

f_sorts(_=_, [T,T], bool, 'T=T'(T)) :- !.
f_eval('T=T'(_), X=Y) := R :- !, ( X = Y -> R = 1 ; R = 0 ).
f_smt('T=T'(_)) := '=' :- !.

f_sorts(_\=_, [T,T], bool, 'T\\=T'(T)) :- !.
f_eval('T\\=T'(_), X\=Y) := R :- !, ( X \= Y -> R = 1 ; R = 0 ).
f_smt('T\\=T'(_)) := 'distinct' :- !.

f_sorts(ite(_,_,_), [bool,T,T], T, 'ite(bool,T,T)'(T)) :- !.
f_eval('ite(bool,T,T)'(_), ite(X,Then,Else)) := R :- !, ( X = 1 -> R = Then ; R = Else ).
f_smt('ite(bool,T,T)'(_)) := 'ite' :- !.

% ---------------------------------------------------------------------------
%! ## Bitvectors
%  http://smtlib.cs.uiowa.edu/theories-FixedSizeBitVectors.shtml

f_sorts(+_, [bitvec(Tw)], bitvec(Tw), '+bitvec'(Tw)) :- !.
f_eval('+bitvec'(_Tw), +X) := X :- !.
f_alias(+A) := A.

f_sorts(-_, [bitvec(Tw)], bitvec(Tw), '-bitvec'(Tw)) :- !.
f_eval('-bitvec'(Tw), -X) := R :- !, R0 is -X, R = ~fixwidth(Tw, R0).
f_smt('-bitvec'(_)) := 'bvneg' :- !.

f_sorts(_+_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec+bitvec'(Tw)) :- !.
f_eval('bitvec+bitvec'(Tw), X+Y) := R :- !, R0 is X + Y, R = ~fixwidth(Tw, R0).
f_smt('bitvec+bitvec'(_)) := 'bvadd' :- !.

f_sorts(_-_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec-bitvec'(Tw)) :- !.
f_eval('bitvec-bitvec'(Tw), X-Y) := R :- !, R0 is X - Y, R = ~fixwidth(Tw, R0).
f_smt('bitvec-bitvec'(_)) := 'bvsub' :- !.

f_sorts(_*_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec*bitvec'(Tw)) :- !.
f_eval('bitvec*bitvec'(Tw), X*Y) := R :- !, R0 is X * Y, R = ~fixwidth(Tw, R0).
f_smt('bitvec*bitvec'(_)) := 'bvmul' :- !.

f_sorts(_<<_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec<<bitvec'(Tw)) :- !.
f_eval('bitvec<<bitvec'(Tw), X<<Y) := R :- !,
    ( Y > Tw -> R0 = 0 ; R0 is X << Y ), R = ~fixwidth(Tw, R0).
f_smt('bitvec<<bitvec'(_)) := 'bvshl' :- !.

f_sorts(_>>_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec>>bitvec'(Tw)) :- !.
f_eval('bitvec>>bitvec'(_), X>>Y) := R :- !, R is X >> Y.
f_smt('bitvec>>bitvec'(_)) := 'bvlshr' :- !.

f_sorts(ashr(_,_), [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'ashr(bitvec,bitvec)'(Tw)) :- !.
f_eval('ashr(bitvec,bitvec)'(Tw), ashr(X,Y)) := R :- !,
    % Like >> but it sets all upper bits to 1 using (-1)<<Tw if needed
    R0 is ~signext(Tw, X) >> Y,
    R = ~fixwidth(Tw, R0).
f_smt('ashr(bitvec,bitvec)'(_)) := 'bvashr' :- !.

f_sorts(_/\_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec/\\bitvec'(Tw)) :- !.
f_eval('bitvec/\\bitvec'(_), X/\Y) := R :- !, R is X /\ Y.
f_smt('bitvec/\\bitvec'(_)) := 'bvand' :- !.

f_sorts(_\/_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec\\/bitvec'(Tw)) :- !.
f_eval('bitvec\\/bitvec'(_), X\/Y) := R :- !, R is X \/ Y.
f_smt('bitvec\\/bitvec'(_)) := 'bvor' :- !.

f_sorts(_#_, [bitvec(Tw),bitvec(Tw)], bitvec(Tw), 'bitvec#bitvec'(Tw)) :- !.
f_eval('bitvec#bitvec'(_), X#Y) := R :- !, R is X # Y.
f_smt('bitvec#bitvec'(_)) := 'bvxor' :- !.

% unsigned comparison

f_sorts(uge(_,_), [bitvec(Tw),bitvec(Tw)], bool, 'uge(bitvec,bitvec)'(Tw)) :- !.
f_eval('uge(bitvec,bitvec)'(Tw), uge(X,Y)) := R :- !,
    ( ~unsigned(Tw,X) >= ~unsigned(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('uge(bitvec,bitvec)'(_)) := 'bvuge' :- !.

f_sorts(ug(_,_), [bitvec(Tw),bitvec(Tw)], bool, 'ug(bitvec,bitvec)'(Tw)) :- !.
f_eval('ug(bitvec,bitvec)'(Tw), ug(X,Y)) := R :- !,
    ( ~unsigned(Tw,X) > ~unsigned(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('ug(bitvec,bitvec)'(_)) := 'bvugt' :- !.

f_sorts(ul(_,_), [bitvec(Tw),bitvec(Tw)], bool, 'ul(bitvec,bitvec)'(Tw)) :- !.
f_eval('ul(bitvec,bitvec)'(Tw), ul(X,Y)) := R :- !,
    ( ~unsigned(Tw,X) < ~unsigned(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('ul(bitvec,bitvec)'(_)) := 'bvult' :- !.

f_sorts(ule(_,_), [bitvec(Tw),bitvec(Tw)], bool, 'ule(bitvec,bitvec)'(Tw)) :- !.
f_eval('ule(bitvec,bitvec)'(Tw), ule(X,Y)) := R :- !,
    ( ~unsigned(Tw,X) =< ~unsigned(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('ule(bitvec,bitvec)'(_)) := 'bvule' :- !.

% signed comparison

f_sorts(_>=_, [bitvec(Tw),bitvec(Tw)], bool, 'bitvec>=bitvec'(Tw)) :- !.
f_eval('bitvec>=bitvec'(Tw), X>=Y) := R :- !,
    ( ~signext(Tw,X) >= ~signext(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('bitvec>=bitvec'(_)) := 'bvsge' :- !.

f_sorts(_>_, [bitvec(Tw),bitvec(Tw)], bool, 'bitvec>bitvec'(Tw)) :- !.
f_eval('bitvec>bitvec'(Tw), X>Y) := R :- !,
    ( ~signext(Tw,X) > ~signext(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('bitvec>bitvec'(_)) := 'bvsgt' :- !.

f_sorts(_<_, [bitvec(Tw),bitvec(Tw)], bool, 'bitvec<bitvec'(Tw)) :- !.
f_eval('bitvec<bitvec'(Tw), X<Y) := R :- !,
    ( ~signext(Tw,X) < ~signext(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('bitvec<bitvec'(_)) := 'bvslt' :- !.

f_sorts(_=<_, [bitvec(Tw),bitvec(Tw)], bool, 'bitvec=<bitvec'(Tw)) :- !.
f_eval('bitvec=<bitvec'(Tw), X=<Y) := R :- !,
    ( ~signext(Tw,X) =< ~signext(Tw,Y) -> R = 1 ; R = 0 ).
f_smt('bitvec=<bitvec'(_)) := 'bvsle' :- !.

% ---------------------------------------------------------------------------
%! ## Arrays
% http://smtlib.cs.uiowa.edu/theories-ArraysEx.shtml

% TODO: Remove?

f_sorts(element(_,_,_), [array(Kt,Vt),Kt,Vt], bool, 'element(Kt,Vt)'(Kt,Vt)) :- !.
f_alias(element(A,B,C)) := (select(A,B)=C) :- !.

f_sorts(update(_,_,_,_), [array(Kt,Vt),Kt,Vt,array(Kt,Vt)], bool, 'update(Kt,Vt)'(Kt,Vt)) :- !.
f_alias(update(A,B,C,A2)) := (store(A,B,C)=A2) :- !.

% TODO: currently only for translation, not fully supported, use element/3
f_sorts(select(_,_), [array(Kt,Vt),Kt], Vt, 'select(Kt,Vt)'(Kt,Vt)) :- !.
f_smt('select(Kt,Vt)'(_,_)) := 'select' :- !.
%
f_sorts(store(_,_,_), [array(Kt,Vt),Kt,Vt], array(Kt,Vt), 'store(Kt,Vt)'(Kt,Vt)) :- !.
f_smt('store(Kt,Vt)'(_,_)) := 'store' :- !.

% ---------------------------------------------------------------------------
% Support for evaluation

% Use Size-bit mask
% (note: silent under/overflow is required here)
fixwidth(Size,N) := R :- R is ((1<<Size)-1)/\N.

% Extend sign bit from Size-bit to unbound arithmetic
signext(Size,N) := R :-
    ( 0 =:= N /\ (1<<(Size-1)) -> % sign bit is unset
        R = N
    ; SignBits is ((-1)<<Size),
      R is (N \/ SignBits)
    ).

% Unsigned sign bit from Size-bit to unbound arithmetic
unsigned(_Size,N) := N. % TODO: nothing if the default representation uses to_bv/3

% ---------------------------------------------------------------------------
%! # Constraint store
% TODO: merge with xclp_rt.pl

:- use_module(engine(internals), ['$global_vars_get'/2, '$global_vars_set'/2]). % (reserve 20)
% (very low-level, see mutables.pl implementation for details)
:- use_module(engine(internals), ['$setarg'/4]).

% The buffer constraint is implemented as a pair of global logical
% variables:
%
%   global 20: xc(_,bc(Head),bc(Tail),_)

xc_state(ciaosmt, XState) :-
    '$global_vars_get'(20,V0),
    ( V0=0 -> % (not initialized)
        XState = xc(_,_,_,_),
        '$global_vars_set'(20, XState),
        xcs_reset_buffer(ciaosmt) % TODO: new
    ; '$global_vars_get'(20,XState)
    ).

% Reset (empty) the buffer
xcs_reset_buffer(XCS) :-
    xc_state(XCS, XState),
    XState = xc(_,_,_,_),
    '$setarg'(2, XState, bc(Constraints), on),
    '$setarg'(3, XState, bc(Constraints), on).

% xcs_flush_buffer(+XCS, -Constraints):
%   Obtain constraint list and reset the buffer
xcs_flush_buffer(XCS, Constraints)  :-
    xc_state(XCS, XState),
    XState = xc(_,bc(Constraints),bc([]),_), % (head,[]), close
    !,
    xcs_reset_buffer(XCS).
xcs_flush_buffer(XCS, []) :- % (first call)
    xcs_reset_buffer(XCS).

% Enqueue a new constraint
xcs_queue_constraints(XCS, Cs) :-
    xc_state(XCS, XState),
    XState = xc(_,_,BC,_),
    BC = bc(Constraints),
    '$setarg'(3, XState, bc(Constraints0), on),
    append(Cs, Constraints0, Constraints).

% :- export({}/1).
% {Constraints} :-
%     conj_to_list(Constraints,Cs,[]),
%     xcs_queue_constraints(ciaosmt, Cs).

conj_to_list(A, Xs, Xs0) :- var(A), !, Xs=[A|Xs0].
conj_to_list((A,B), Xs, Xs0) :- !,
    conj_to_list(A, Xs, Xs1),
    conj_to_list(B, Xs1, Xs0).
conj_to_list(true, Xs, Xs0) :- Xs=Xs0.
conj_to_list(A, Xs, Xs0) :- Xs=[A|Xs0].

:- export(add_constraints/1).
:- pred add_constraints/1 # "Add constraint @var{Constraints} to the
   store (from the term representation, useful for meta-programming)".
add_constraints(Constraints) :-
    xcs_queue_constraints(ciaosmt, Constraints).

% ---------------------------------------------------------------------------
%! # Solve constraints

:- export(solve/1).
:- pred solve(Vars) # "Unqueue and solve constraints, assign values to
   variables @var{Vars}. Fail on unsat, throw exception @tt{unknown}
   on unknown".
% TODO: solve all constraints or only those relevant to Vars? allow both?

solve(Vars) :-
    xcs_flush_buffer(ciaosmt, Constraints),
    run_solver(Constraints, Status, get_model),
    sat_status(Status),
    erase_constraints(Vars, _, Map),
    assign_map(Map).

assign_map([]).
assign_map([X=X|Xs]) :- assign_map(Xs).

:- export(checksat/0).
:- pred checksat # "Only check for satisfiability (without fixing
   solutions or dropping constraints). Fail on unsat, throw exception
   @tt{unknown} on unknown".

checksat :-
    xcs_flush_buffer(ciaosmt, Constraints),
    run_solver(Constraints, Status, check_sat),
    sat_status(Status),
    % TODO: requeue the constraints, inefficient?
    xcs_queue_constraints(ciaosmt, Constraints).

sat_status(Status) :-
    ( Status = unsat -> fail
    ; Status = unknown -> throw(unknown) % No solution is found (timeout, etc.)
    ; Status = sat -> true
    ).

:- export(try_solve/1).
:- pred try_solve(Status) # "Like @pred{solve/2}, but the model assignment
   can be undone with @pred{erase_constraints/2}.
   @var{Status} is:
   @begin{itemize}
   @item sat: the formula is satisfiable (model is assigned to variables as attributes)
   @item unsat: formula is unsatisfiable
   @item unknown: if no model is found (e.g., due to timeout)
   @end{itemize}".

try_solve(Status) :-
    xcs_flush_buffer(ciaosmt, Constraints),
    run_solver(Constraints, Status, get_model).

run_solver(Goal, Status, Mode) :-
    % display(user_error, gm(Goal)), nl(user_error),
    %prop_array(Goal),
    smt_get_solver(Solver),
    smt_begin(Solver),
    smt_defs(Solver),
    smt_add(Solver, Goal, RevDic),
    smt_check_sat(Solver, Result),
    ( sat_result(Result) -> true
    ; throw(error(bad_status(Result), run_solver/3))
    ),
    Status = Result,
    ( Mode = get_model, Status = sat ->
        smt_get_model(Solver, RevDic, Model),
        % \+ \+ ( numbervars(Model,0,_), format("Goal: ~q~nRevDic: ~q~n", [Goal, RevDic]) ), % (verbose)
        smt_end(Solver),
        ( assign_model(Model),
          % TODO: (it may not be needed if we get the arrays directly from SMT)
          assign_arr(Goal) ->
            true
        ; % Note: this should not happen
          %display(user_error, g(Goal)), nl(user_error),
          throw(error(could_not_reconstruct_model, get_model/1))
        )
    ; true
    ).

sat_result(sat).
sat_result(unsat).
sat_result(unknown).

% % TODO: Very incomplete... implement real propagation or use a SMT
% %   propagate some array constraints for registers
% % TODO: use something better than assoc (attr?)
% prop_array(Goal) :-
%     empty_assoc(Dic0),
%     prop_array_(Goal, Dic0).
% 
% prop_array_([], _).
% prop_array_([element(A,K,V)|Cs], Dic0) :-
%     datatype0(K,_,_), var(V), !, % TODO: ad-hoc for 'regs'! Fixme!
%     ( get_assoc((A,K), Dic0, V0) -> V = V0, Dic1 = Dic0
%     ; put_assoc((A,K), Dic0, V, Dic1)
%     ),
%     prop_array_(Cs, Dic1).
% prop_array_([_|Cs], Dic) :-
%     prop_array_(Cs, Dic).

assign_model([]).
assign_model([assign(X,Ty,V)|Cs]) :-
    X = ~newsym(V,Ty),
    assign_model(Cs).

% Repopulate arrays from goal
% TODO: it may not be needed if we get the arrays directly from SMT
% TODO: buggy, it does not work with select/store and it is sensitive to order
assign_arr([]).
assign_arr([C|Cs]) :-
    ( assign_arr_(C) -> true
    ; throw(bug_failed_assign_arr_(C)) % TODO: this should not happen
    ),
    assign_arr(Cs).

assign_arr_(Var::Ty) :- Ty=array(_,_), !,
    declvar(Var, Ty).
assign_arr_(element(A,K,V)) :- !,
    % TODO: make eval_select_u/4 bidirectional?
    eval_select_u(A,K,V0,V0t),
    ( type(V0,var) ->
        %display(user_error, v), nl(user_error),
        V0 = ~unbox(V) % TODO: ugly?
    ; type(V0,attv) ->
        get_attribute(V0, v(Vv,Ty)),
        ( get_attribute(V, v(Vv1,Ty1)) -> Vv=Vv1, Ty=Ty1 % TODO: ugly?
        ; V=V0 % TODO: ugly?
        )
    ; V = ~box(V0t,V0) % TODO: ugly?
    ).
assign_arr_(update(A0,K,V,A)) :- !,
    ( type(A, attv) -> detach_attribute(A) ; true ), % TODO: ugly
    A = ~eval(store(A0,K,V)).
assign_arr_(_).

% ---------------------------------------------------------------------------
%! ## Erase constraints

:- use_module(library(terms_vars)).
:- use_module(library(lists), [append/3]).

:- export(erase_constraints/3).
% Remove constraints from X, keep declarations and constraints in
% Goal, and concrete model assignments in Map
erase_constraints(X, Goal, Map) :-
    varset(X, Vars),
    unassign(Vars, Goal, Map).

% Unassign concrete values assigned to symbolic variables, keep
% declarations in Decls, and obtain the model assignment in the Map
% argument.
unassign([], [], []).
unassign([X|Xs], Ds, Map) :-
    ( get_attribute(X, v(_,Xt)) -> 
        Ds = [(X::Xt)|Ds1]
    ; Ds = Ds1
    ),
    ( unassignvar(X,V,Ty) ->
        ( Ty=array(Kt,Vt) ->
            V2 = ~array_elems_(V),
            elems_to_constrs(V2,X,Kt,Vt,Ds1,Ds0),
            append(~varset(V2), Xs, Xs2), % push child vars
            Map = Map0
        ; nonvar(V) -> % assume bitvec
            Map = [X=V|Map0], Ds1 = Ds0, Xs2 = Xs
        ; Map = Map0, Ds1 = Ds0, Xs2 = Xs % (ignore if V is free)
        )
    ; Map = Map0, Ds1 = Ds0, Xs2 = Xs
    ),
    unassign(Xs2, Ds0, Map0).

% Remove attribute from X, get value V and type Ty
% (fail otherwise)
unassignvar(X, V, Ty) :-
    type(X,attv), get_attribute(X, v(V0,Ty0)),
    detach_attribute(X),
    V = V0,
    Ty = Ty0.

elems_to_constrs([],_,_,_) --> [].
elems_to_constrs([K=V|D],Arr,Kt,Vt) -->
    { K1 = ~box(Kt,K) },
    [element(Arr,K1,~box(Vt,V))],
    elems_to_constrs(D,Arr,Kt,Vt).

% ---------------------------------------------------------------------------
%! ## External SMT solver process

% TODO: add other solvers

:- use_module(library(port_reify)).
:- use_module(library(process)).
:- use_module(library(streams), [close/1]).
:- use_module(library(assoc)).
:- use_module(engine(messages_basic), [message/2]).
:- use_module(library(system), [file_exists/1, current_executable/1, find_executable/2]).
:- use_module(library(pathnames), [path_concat/3, path_split/3]).

:- use_module(.(smtlib)).

:- use_module(engine(internals), [ciao_root/1]).

% TODO: use Ciao builder 3rd party support
find_bin(Cmd, Path) :-
    % relative to the current executable
    current_executable(ExecPath),
    path_split(ExecPath, Dir, _),
    ( Path0 = ~path_concat(Dir, Cmd)
    ; Path0 = ~path_concat(~path_concat(Dir, 'third-party/bin'), Cmd)
    ; Path0 = ~path_concat(~path_concat(~ciao_root, 'third-party/bin'), Cmd)
    ),
    file_exists(Path0),
    !,
    Path = Path0.
find_bin(Cmd, Path) :- % in the PATH
    find_executable(Cmd, Path).

:- data z3_bin_/1.
z3_bin := Path :-
    ( z3_bin_(Path0) -> true
    ; find_bin('z3', Path0), set_fact(z3_bin_(Path0))
    ),
    Path = Path0.

:- data has_smt_/1.
has_smt :- 
    ( has_smt_(X) -> true
    ; ( file_exists(~z3_bin) -> X = yes
      ; X = no,
        message(warning, ['could not detect any external SMT solver'])
      ),
      assertz_fact(has_smt_(X))
    ),
    X = yes.

% :- use_module(library(format)).
:- use_module(engine(stream_basic), [flush_output/1]).

:- data z3_process/3.

smt_get_solver(Solver) :-
    Solver = solver(PSolver, In, Out),
    ( z3_process(PSolver, In, Out) ->
        true
    ; has_smt ->
        process_call(~z3_bin, ['-in'|~solver_args],
          [stdin(stream(In)), stdout(stream(Out)), status(_), background(PSolver)]),
        % message(error, ['starting z3']),
        assertz_fact(z3_process(PSolver, In, Out))
    ; throw(error(no_solver, smt_get_solver/1))
    ).

% TODO: document 'hard_timeout' (currently unused)
solver_args(Args) :-
    ( get_solver_opt(hard_timeout, HardTO) ->
        HardTOsec is ceiling(HardTO/1000.0), % seconds from ms, no float is allowed
        atom_codes(OptTO, "-T:"||(~number_codes(HardTOsec))),
        Args = [OptTO]
    ; Args = []
    ).

smt_close :-
    z3_process(PSolver, In, Out), !,
    close(In),
    close(Out),
    process_join(PSolver),
    retractall_fact(z3_process(_,_,_)).
smt_close.

% ---------------------------------------------------------------------------
%! ## Add (assert in SMT jargon) to external solver

smt_add(Solver, Goal, RevDic) :-
    Solver = solver(_PSolver, In, _Out),
    % TODO: add flag to enable debug
    % ( \+ \+ tell_cmds(user_output, Goal, _) -> true ; true ), % (verbose)
    smt_add_(In, Goal, RevDic),
    flush_output(In).

% Rewrite goal and tell SMT commands (declarations, assert, check sat, get model, etc.)
smt_add_(S, Goal, RevDic) :-
    empty_assoc(Dic0),
    ( ct_gs(Goal, Dic0, _Dic, Decls, []) -> true
    ; throw(error(failed, ct_gs/5))
    ),
    %display(user_error, ct_gs2(Goal)), nl(user_error),
    empty_assoc(RevDic0),
    namedecls(Decls, 0, RevDic0, RevDic),
    \+ \+ (
      unifnames(RevDic),
      rw_cmds(Decls, Goal, Cmds, []),
      wr_es(Cmds, S)).

% give names to declared variables (assume no repetitions)
namedecls([], _, Dic, Dic).
namedecls([decl(K,X,Ty)|Cs], Idx, Dic0, Dic) :-
    Idx1 is Idx + 1,
    put_assoc(Idx, Dic0, decl(K,X,Ty), Dic1),
    namedecls(Cs, Idx1, Dic1, Dic).

% (for convenience) unify vars with its name and type
unifnames(Dic) :-
    assoc_to_list(Dic, KVs),
    unifnames_(KVs).

unifnames_([]).
unifnames_([Idx-decl(_K,X,Ty)|KVs]) :- X = vt(Idx,Ty), unifnames_(KVs).

% ---------------------------------------------------------------------------
%! ## Type check pass

% TODO: add an environment stack instead of Dic

ct_gs([], Dic, Dic) --> [].
ct_gs([C|Cs], Dic0, Dic) -->
    ct_g(C, Dic0, Dic1),
    ct_gs(Cs, Dic1, Dic).

ct_g(C, _, _) --> { var(C) }, !, { throw(error(unbound, ct_g/5)) }.
ct_g((X::Xt), Dic0, Dic) --> !,
    ct_declvar(var, X, Xt, Dic0, Dic).
ct_g(define_fun(X,Ty,Def), Dic0, Dic) --> !,
    { X=..[_F|Decls] },
    ct_args(Decls, Dic0, Dic1),
    ct_e(Def, DefTy, Dic1, Dic),
    { \+ DefTy = Ty -> throw(error(define_fun_type_mismatch(DefTy,Ty), ct_g/5))
    ; true
    }.
ct_g(C, Dic0, Dic) -->
    ct_e(C, Xt, Dic0, Dic),
    { Xt = bool -> true
    ; throw(error(not_p(Xt,C), ct_g/5))
    }.

ct_e(X, Xt, Dic0, Dic) --> { var(X) }, !,
    ct_declvar(var, X, Xt, Dic0, Dic). % TODO: some vars appear here without a declvar/2, is it OK?
ct_e(X, Xt, Dic0, Dic) --> { X=vt(_Idx,Xt0) }, !, { Xt=Xt0, Dic=Dic0 }. % TODO: internal, needed now?
ct_e(X, Xt, Dic0, Dic) --> { integer(X) }, !, { Xt=int, Dic=Dic0 }. % TODO: add real and float?
ct_e(true, Xt, Dic0, Dic) --> !, { Xt=bool, Dic=Dic0 }.
ct_e(false, Xt, Dic0, Dic) --> !, { Xt=bool, Dic=Dic0 }.
ct_e(bv(_,Xw), Xt, Dic0, Dic) --> !, { Xt=bitvec(Xw), Dic=Dic0 }.
ct_e(extract(High,Low,A), Xt, Dic0, Dic) --> !,
    ct_e(A, At, Dic0, Dic),
    { At = bitvec(_) -> true % TODO: check size?
    ; throw(error(expected_bitvector, ct_e/6))
    },
    { Size is High-Low+1, Xt=bitvec(Size) }.
ct_e(X, Xt, Dic0, Dic) --> { datatype0(X,Xt0,_) }, !, { Xt=Xt0, Dic=Dic0 }.
ct_e(forall(Decls,G), Xt, Dic0, Dic) --> { nonvar(Decls) }, !, % TODO: use environment stack, rename variables?
    ct_args(Decls, Dic0, Dic1),
    ct_e(G, Xt, Dic1, Dic).
ct_e(let(Defs,G), Xt, Dic0, Dic) --> { nonvar(Defs) }, !, % TODO: use environment stack, rename variables?
    ct_letargs(Defs, Dic0, Dic1),
    ct_e(G, Xt, Dic1, Dic).
ct_e(X, Xt, Dic0, Dic) -->
    ct_f(X, Xt, Dic0, Dic).

ct_f(X, Xt, Dic0, Dic) --> { X1 = ~f_alias(X) }, !,
    ct_f(X1, Xt, Dic0, Dic).
ct_f(X, Xt, Dic0, Dic) -->
    { X=..[F|As] },
    ct_es(As, Ats, Dic0, Dic),
    %{ display(user_error, ct_f(X, Ats)), nl(user_error) },
    ( { fun_sorts(X, Ats, Xt0) } -> % user function
        { Xt=Xt0 }
    ; { f_sorts(X, Ats, Xt0, _Vers) } -> % found sort match
        { Xt=Xt0 }
    ; %{ display(user_error, cannot_match_sort(X)), nl(user_error) },
      { throw(error(cannot_match_sort(F, Ats), ct_f/2)) }
    ).

ct_es([],[],Dic,Dic) --> [].
ct_es([X|Xs],[Xt|Xts],Dic0,Dic) -->
    ct_e(X,Xt,Dic0,Dic1),
    ct_es(Xs,Xts,Dic1,Dic).

% Kind: var - Variable declaration (variables)
%       arg - Argument declaration (for functions and quantifiers)
ct_declvar(Kind, A, Type, Dic0, Dic) -->
    ( { get_assoc(A, Dic0, Type0) } -> { Dic=Dic0, Type=Type0 } % TODO: error?
    ; { put_assoc(A, Dic0, Type, Dic) }, [decl(Kind,A,Type)]
    ).

% Arguments (for functions and quantifiers)
ct_args([], Dic, Dic) --> !.
ct_args([D|Decls], Dic0, Dic) --> { nonvar(D), D=(X::Xt) },
    ct_declvar(arg, X, Xt, Dic0, Dic1),
    ct_args(Decls, Dic1, Dic).

% Definitions for let expressions
ct_letargs([], Dic, Dic) --> !.
ct_letargs([D|Defs], Dic0, Dic) --> { nonvar(D), D=(V=X) },
    ct_e(X, Xt, Dic0, Dic1),
    ct_declvar(arg, V, Xt, Dic1, Dic2),
    ct_letargs(Defs, Dic2, Dic).

% ---------------------------------------------------------------------------
%! ## Rewrite as sexp

rw_cmds(Decls, Goal) -->
    %{ display(user_error, rw_cmds(Decls,Goal)), nl(user_error) },
    rw_decls(Decls),
    rw_gs(Goal).

rw_decls([]) --> [].
rw_decls([decl(K,X,Type)|Ds]) -->
    rw_decl(K,X,Type),
    rw_decls(Ds).

rw_decl(arg,_,_) --> !.
rw_decl(_,_,Type) --> { ignoredecl(Type) }, !.
rw_decl(_K,X,Type) -->
    { nonvar(X), X=vt(Idx,_) -> Xr=vr(Idx)
    ; throw(error(unknown_var, rw_decl/4))
    },
    { TypeR = ~rw_ty(Type) },
    [sexp(['declare-fun',Xr,sexp([]),TypeR])].

ignoredecl(array(Type,_)) :- datatype_ty(Type). % TODO: ad-hoc for 'regs' Fixme!

rw_gs([]) --> [].
rw_gs([C|_]) --> { var(C) }, !, { throw(error(unbound, rw_gs/3)) }.
rw_gs([C|Cs]) --> { C = (_::_) }, !, rw_gs(Cs).
rw_gs([C|Cs]) --> { rw_ignore_g(C) }, !, rw_gs(Cs).
rw_gs([C|Cs]) -->
    { R = ~rw_g(C) }, [R], rw_gs(Cs).

rw_ignore_g(X) :-
    ( X = element(_,K,_) 
    ; X = update(_,K,_,_)
    ),
    datatype0(K,_,_), % TODO: ad-hoc for 'regs' Fixme!
    !.

rw_g(define_fun(X,Ty,Def)) := R :- !,
    X=..[F|Decls],
    rw_args(Decls, As),
    rw_e(Def, DefR, _Rt),
    TypeR = ~rw_ty(Ty),
    R = sexp(['define-fun', F, sexp(As), TypeR, DefR]).
rw_g(X) := R :-
    rw_e(X, R0, Rt),
    ( Rt = bool -> true
    ; throw(error(not_p, rw_g/2))
    ),
    R = sexp(['assert',R0]).

rw_e(X,_,_) :- var(X), !,
    throw(error(could_not_rw_var, rw_e0/3)).
rw_e(A,R,Rt) :- A=vt(Idx,At), !, R = vr(Idx), Rt=At.
rw_e(X,R,Rt) :- integer(X), !, % TODO: add real and float?
    R = X,
    Rt = int.
rw_e(true,R,Rt) :- !, R = true, Rt = bool.
rw_e(false,R,Rt) :- !, R = false, Rt = bool.
rw_e(bv(X,Xw),R,Rt) :- !,
    Rt = bitvec(Xw),
    R = ~ty_smtval(Rt,X).
rw_e(extract(High,Low,A),R,Rt) :- !,
    rw_e(A,Ar,_At), % TODO: check type again?
    R = sexp([sexp(['_','extract',High,Low]), Ar]),
    Size is High-Low+1,
    Rt = bitvec(Size).
%rw_e(X,_) := X :- datatype0(X,...), !. % TODO: review
rw_e(forall(Decls,G),R,Rt) :- !,
    rw_args(Decls, As),
    rw_e(G, Gr, Rt),
    R = sexp(['forall', sexp(As), Gr]).
rw_e(let(Defs,G),R,Rt) :- !,
    rw_letargs(Defs, As),
    rw_e(G, Gr, Rt),
    R = sexp(['let', sexp(As), Gr]).
rw_e(A,R,Rt) :-
    rw_f(A, R, Rt).

rw_args([],[]).
rw_args([(X::_)|Decls],[A|As]) :-
    nonvar(X), X=vt(Idx,Type),
    TypeR = ~rw_ty(Type),
    A = sexp([vr(Idx), TypeR]),
    rw_args(Decls, As).

rw_letargs([],[]).
rw_letargs([V=X|Defs],[A|As]) :-
    nonvar(V), V=vt(Idx,_),
    rw_e(X, Xr, _Xt),
    A = sexp([vr(Idx), Xr]),
    rw_letargs(Defs, As).

rw_f(X, R, Tr) :- X1 = ~f_alias(X), !,
    rw_f(X1, R, Tr).
rw_f(X, R, Tr) :-
    X=..[F|As],
    rw_es(As,As2,Ats),
    ( fun_sorts(X, Ats, Tr0) -> % user function
        N = F, Ts=Ats, Tr=Tr0
    ; f_sorts(X, Ats, Tr0, Vers) -> % found sort match
        Ts=Ats, Tr=Tr0,
        ( N = ~f_smt(Vers) -> true
        ; throw(error(unknown_f_smt, rw_f/2))
        )
    ; throw(error(cannot_match_sort(F, Ats), rw_f/2))
    ),
    R = sexp([N|As2]).

rw_es([],[],[]).
rw_es([X|Xs],[R|Rs],[Rt|Rts]) :-
    rw_e(X,R,Rt),
    rw_es(Xs,Rs,Rts).

rw_ty(Type, TypeR) :-
    ( var(Type) -> throw(error(type_unbound(Type), rw_ty/2))
    ; TypeR = ~ty_smt(Type) -> true
    ; throw(error(unsupported_type(Type), rw_ty/2))
    ).

% ---------------------------------------------------------------------------
%! ## Send/receive S-exp to/from the solver

smt_send(solver(_,In,_), Cmds) :-
    wr_es(Cmds, In),
    flush_output(In).

smt_recv(Solver, Answer) :-
    Solver = solver(_PSolver, _In, Out),
    %% format("SMT output: ~s~n", [Out]), % (verbose)
    rd_answer(Out, Answer).

rd_answer(S, X) :-
    ( rd_e(S, X0) -> true
    ; throw(error(parse, smt_recv/2))
    ),
    ( X0 = sexp(['error', string(_Str)]) ->
%           message(warning, ['[smt] ', $$(Str)]),
        rd_answer(S, X)
    ; X = X0
%         message(error, ['rda: ', X])
    ).

% ---------------------------------------------------------------------------
%! ## Begin/end external solver session

smt_begin(Solver) :-
    rw_begin(Cmds, []),
    smt_send(Solver, Cmds).

rw_begin -->
    [sexp(['reset'])].
    %rw_tydef(bitvec(64)),
    %rw_tydef(array(bitvec(64),bitvec(64))).

% TODO: only if ty_smtdef is defined!
%rw_tydef(Ty) -->
%    { Def = sexp(['define-sort', ~ty_smtid(Ty), sexp([]), ~ty_smtdef(Ty)]) },
%    [Def].

:- compilation_fact(keep_alive).
:- if(defined(keep_alive)).
smt_end(_). % keep alive
:- else.
% % (Exit the solver)
smt_end(Solver) :- smt_send(Solver, [sexp(['exit'])]), smt_close.
:- endif.

smt_defs(Solver) :-
    ( % (failure-driven loop)
      fun_def(X, Ty, Def),
        smt_add(Solver, [define_fun(X, Ty, Def)], _RevDic),
        fail
    ; true
    ).

% ---------------------------------------------------------------------------
%! ## Query satisfiability/model from external solver

% Check satisfiability
smt_check_sat(Solver, Result) :-
    ( get_solver_opt(timeout, TO) ->
        % (value 0 is treated as no timeout)
        smt_send(Solver, [sexp(['set-option', ':timeout', TO])])
    ; true
    ),
    smt_send(Solver, [sexp(['check-sat'])]),
    smt_recv(Solver, Result0),
    ( Result0 = unsat -> Result = unsat
    ; Result0 = sat -> Result = sat
    ; Result0 = unknown -> Result = unknown
    ; throw(error(unknown_answer(Result0), smt_check_sat/2))
    ).

% Get model and assign to variables
smt_get_model(Solver, RevDic, Model) :-
    smt_send(Solver, [sexp(['get-model'])]),
    smt_recv(Solver, Answer),
    ( Answer = sexp([model|Model0]) ->
        Model = ~dump_model(Model0, RevDic)
    ; throw(error(unknown_answer(Answer), smt_get_model/2))
    ).

% :- use_module(library(streams)).

dump_model([sexp(['define-fun', vr(Idx), sexp([]), TyR, ValR])|Xs], RevDic, [C|Cs]) :-
    get_assoc(Idx, RevDic, decl(_,X,_)),
    dump_val(TyR, ValR, Ty, V),
    !,
    C = assign(X,Ty,V),
    dump_model(Xs, RevDic, Cs).
dump_model([_X|Xs], RevDic, Cs) :- !, % TODO: extend!
    % displayq(user_error, _X), nl(user_error),
    dump_model(Xs, RevDic, Cs).
dump_model([], _, []).

dump_val(sexp(['_','BitVec',VwAtm]), ValR, Ty, V) :-
    % TODO: fix smtlib.pl to parse numbers properly (any issue with floats?)
    atom_codes(VwAtm, VwCs), number_codes(Vw, VwCs),
    ValR = bitvecval(V0,_),
    !,
    Ty = bitvec(Vw),
    V = V0.
dump_val('Int', sexp(['-',ValR]), Ty, V) :-
    % TODO: fix smtlib.pl to parse numbers properly (any issue with floats?)
    atom_codes(ValR, ValCs), number_codes(V0, ValCs),
    !,
    Ty = int,
    V is -V0.
dump_val('Int', ValR, Ty, V) :-
    % TODO: fix smtlib.pl to parse numbers properly (any issue with floats?)
    atom_codes(ValR, ValCs), number_codes(V0, ValCs),
    !,
    Ty = int,
    V = V0.
