:- module(_, [], [assertions, fsyntax, datafacts, hiord]).

:- use_module(concolic(concolic)).
:- use_module(concolic(symbolic)).

% TODO: simpler conc_cond (X=A works for reified comparisons, etc. it should be easier)

% TODO: test constraints
% TODO: test get model

% ---------------------------------------------------------------------------
% Prolog search with traces. Produces different traces on backtracking
% (note that this is not concolic search!)

:- export(test1/1).
test1(Trace) :-
    with_trace(Trace, test1_).

test1_ :-
    trace(a),
    ( trace(b1) ; trace(b2) ), % Prolog nondet
    trace(c).

% ---------------------------------------------------------------------------
% Concolic search with traces. Do not produce different traces since there
% are no path conditions to negate.

:- export(test1c/1).
test1c(Trace) :-
    conc_call(test1_, _, Trace).

test1c_ :-
    trace(a),
    ( trace(b1) ; trace(b2) ), % Prolog nondet under concolic (cut!)
    trace(c).

% ---------------------------------------------------------------------------
% Concolic search with path conditions

:- export(test2/2).
test2(X, Trace) :-
    conc_call(test2_(X), [X], Trace).

test2_(X) :-
    trace(a),
    V = ~conc_cond(X=1), % path condition
    ( V=1 -> trace(b1)
    ; trace(b2)
    ),
    trace(c).
