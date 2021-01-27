:- module(_, [], [fsyntax]).

% Tests for ciaosmt

:- op(978, xfx,(::)).
:- op(700, xfx,(#=)).
:- op(700, xfx,(#\=)).
:- op(700, xfx,(#<)).
:- op(700, xfx,(#>)).
:- op(700, xfx,(#=<)).
:- op(700, xfx,(#>=)).

X::Y :- add_constraints([X::Y]).
X #= Y :- add_constraints([X=Y]).
X #\= Y :- add_constraints([X\=Y]).
X #< Y :- add_constraints([X<Y]).
X #> Y :- add_constraints([X>Y]).
X #=< Y :- add_constraints([X=<Y]).
X #>= Y :- add_constraints([X>=Y]).

forall(Decls, Constrs) :- add_constraints([forall(Decls,Constrs)]).

:- use_module(concolic(ciaosmt)).
:- use_module(library(streams)).
:- use_module(library(write)).
:- use_module(library(format)).

% ---------------------------------------------------------------------------

:- export(test_bv/1).
% X=13 % TODO: wrong! it should be bv(13,64), do not unify with unboxed
test_bv(X) :-
    X>>bv(2,64) #= bv(3,64),
    X/\((bv(1,64)<<bv(2,64))-bv(1,64)) #= bv(1,64),
    solve(X).

:- export(test_int1/1).
test_int1(X) :-
    X#>10, X#<12,
    solve([X]).

:- export(test_int2/2).
test_int2(X, Y) :-
    X+Y#=3, X-Y#=1,
    solve([X,Y]).

% ---------------------------------------------------------------------------

% Expected solution: [[1,2,3,4,5],[6,7,8,9,10]]

:- export(test_forall/0).
test_forall :-
    Len = 5,
    A::array(int,int),
    B::array(int,int),
    % Last element of A is less than first element of B
    select(A,Len) #< select(B,1),
    % Elements of A are ordered
    forall([I::int],
           ( I>=1, I<Len -> select(A,I)<select(A,I+1) )),
    % Elements of B are ordered
    forall([I::int],
           ( I>=1, I<Len -> select(B,I)<select(B,I+1) )),
    % Elements of A between 1 and 2*Len
    forall([K::int,P::int],
           ( K>=1, K=<Len,
             P=select(A,K) ->
                 P >= 1, P =< 2*Len )),
        % Elements of B between 1 and 2*Len
    forall([K::int,P::int],
           ( K>=1, K=<Len,
             P=select(B,K) ->
                 P >= 1, P =< 2*Len )),
    A1 #= select(A,1),
    A2 #= select(A,2),
    A3 #= select(A,3),
    A4 #= select(A,4),
    A5 #= select(A,5),
    B1 #= select(B,1),
    B2 #= select(B,2),
    B3 #= select(B,3),
    B4 #= select(B,4),
    B5 #= select(B,5),
    Vars=[[A1,A2,A3,A4,A5],
          [B1,B2,B3,B4,B5]],
    solve(Vars),
    write(Vars), nl.

% ---------------------------------------------------------------------------

% Expected: 0x1000100010011001

:- export(test_fun/0).
test_fun :-
    assert_fun(sum_bits(Input::bitvec(64))::bitvec(1),
        let([T32=extract(31,0,Input)#extract(63,32,Input)],
            let([T16=extract(15,0,T32)#extract(31,16,T32)],
                let([T8=extract(7,0,T16)#extract(15,8,T16)],
                    let([T4=extract(3,0,T8)#extract(7,4,T8)],
                        let([T2=extract(1,0,T4)#extract(3,2,T4)],
                            extract(0,0,T2)#extract(1,1,T2))))))),
    R::bitvec(64),
    sum_bits(R/\bv(0x1010001100010101,64)) #= bv(1,1),
    sum_bits(R/\bv(0x1110011001001100,64)) #= bv(0,1),
    sum_bits(R/\bv(0x0000101110100101,64)) #= bv(1,1),
    solve(R),
    format("0x~16r\n", [R]).

% ---------------------------------------------------------------------------

% Example:
%
% ?- test_fib(5,X).
% 
% X = 8 ? 
% 
% yes
% ?- test_fib(X,8).
% 
% X = 5 ? 

:- export(test_fib/2).
test_fib(X,Y) :- fib(X,Y), solve([X,Y]).

fib(X, Y) :-
    X #>= 0, X #=< 1, Y #= 1, checksat.
fib(X, Y) :-
    X #>= 2, Xm1 #= X-1, Xm2 #= X-2, Y #= Y1+Y2, checksat,
    fib(Xm1, Y1),
    fib(Xm2, Y2).

% ---------------------------------------------------------------------------

% Example:
%
% ?- test_mc(50,X).
% 
% X = 91 ? 

:- export(test_mc/2).
test_mc(X,Y) :- mc(X,Y), solve([X,Y]).

mc(N, M) :-
    N #>= 101, M #= N-10, checksat.
mc(N, M) :-
    N #=< 100, T #= N+11, checksat,
    mc(T, U),
    mc(U, M).

% ---------------------------------------------------------------------------
% SEND+MORE=MONEY
% [S,E,N,D,M,O,R,Y] = [9,5,6,7,1,0,8,2]

:- export(test_mm/1).
test_mm(Xs) :-
    mm(Xs), solve(Xs).

mm([S,E,N,D,M,O,R,Y]) :-
    domain([S,E,N,D,M,O,R,Y], 0, 9),
    0 #< S, 0 #< M,
    all_different([S,E,N,D,M,O,R,Y]),
       S*1000 + E*100 + N*10 + D
     + M*1000 + O*100 + R*10 + E #=
       M*10000 + O*1000 + N*100 + E*10 + Y.

domain([], _, _).
domain([X|Xs], Min, Max) :-
    domain1(X, Min, Max),
    domain(Xs, Min, Max).

domain1(X, Min, Max) :-
    X #>= Min,
    X #=< Max.

all_different([]).
all_different([X|Xs]) :-
    all_different1(Xs,X),
    all_different(Xs).

all_different1([],_).
all_different1([X|Xs],Y) :-
    X #\= Y,
    all_different1(Xs,Y).

% ---------------------------------------------------------------------------
% http://www.hakank.org/minizinc/crypto.mzn
%    Solution:
%    A, B,C, D, E,F, G, H, I, J, K,L,M, N, O, P,Q, R, S,T,U, V,W, X, Y, Z
%    5,13,9,16,20,4,24,21,25,17,23,2,8,12,10,19,7,11,15,3,1,26,6,22,14,18

:- export(test_crypto/1).
test_crypto(Xs) :-
    crypto(Xs), solve(Xs).

crypto(AllLetters) :-
    AllLetters = [A, B, C, _D, E, F, G, H, I, J, K, L, M, N, O, P, Q, R, S, T, U, V, W, X, Y, Z],
    domain(AllLetters, 1, 26),
    BALLET = 45,
    CELLO = 43,
    CONCERT = 74,
    FLUTE = 30,
    FUGUE = 50,
    GLEE = 66,
    JAZZ = 58,
    LYRE = 47,
    OBOE = 53,
    OPERA = 65,
    POLKA = 59,
    QUARTET = 50,
    SAXOPHONE = 134,
    SCALE = 51,
    SOLO = 37,
    SONG = 61,
    SOPRANO = 82,
    THEME = 72,
    VIOLIN = 100,
    WALTZ = 34,
    % % solve satisfy;
    % solve :: int_search(all_letters, first_fail, indomain_median, complete) satisfy;
    all_different(AllLetters),
    ~sum([B,A,L,L,E,T]) #= BALLET,
    ~sum([C,E,L,L,O]) #= CELLO,
    ~sum([C,O,N,C,E,R,T]) #= CONCERT,
    ~sum([F,L,U,T,E]) #= FLUTE,
    ~sum([F,U,G,U,E]) #= FUGUE,
    ~sum([G,L,E,E]) #= GLEE,
    ~sum([J,A,Z,Z]) #= JAZZ,
    ~sum([L,Y,R,E]) #= LYRE,
    ~sum([O,B,O,E]) #= OBOE,
    ~sum([O,P,E,R,A]) #= OPERA,
    ~sum([P,O,L,K,A]) #= POLKA,
    ~sum([Q,U,A,R,T,E,T]) #= QUARTET,
    ~sum([S,A,X,O,P,H,O,N,E]) #= SAXOPHONE,
    ~sum([S,C,A,L,E]) #= SCALE,
    ~sum([S,O,L,O]) #= SOLO,
    ~sum([S,O,N,G]) #= SONG,
    ~sum([S,O,P,R,A,N,O]) #= SOPRANO,
    ~sum([T,H,E,M,E]) #= THEME,
    ~sum([V,I,O,L,I,N]) #= VIOLIN,
    ~sum([W,A,L,T,Z]) #= WALTZ.

% (syntactic)
sum([X]) := R :- !, R = X.
sum([X|Xs]) := X+Y :- Y = ~sum(Xs).

% ---------------------------------------------------------------------------

:- export(test_ack/3).
% 3,1,13
test_ack(Z1,Z2,Z3) :-
    ack(Z1,1,13), solve(Z1),
    ack(3,Z2,13), solve(Z2),
    ack(3,1,Z3), solve(Z3).

ack(0, N, R) :- R #= N+1, checksat.
ack(M, 0, R) :- M #>= 1, M1 #= M-1, checksat, ack(M1, 1, R).
ack(M, N, R) :-
    M #>= 1, N #>= 1,
    N1 #= N-1,
    M1 #= M-1, checksat,
    ack(M, N1, T), ack(M1, T, R).

% ---------------------------------------------------------------------------

% TODO: currently too slow
:- export(test_tak/1).
test_tak(R) :- tak(18, 12, 6, R), solve(R).

tak(X, Y, Z, A) :-
    display(tak(X, Y, Z, A)), nl, fail.
tak(X, Y, Z, A) :-
    X #=< Y,
    Z #= A,
%   Y #= A,
%    solve([X,Y,Z,A]).
    checksat.
tak(X, Y, Z, A) :-
    X #>= Y+1,
    X1 #= X-1,
    Y1 #= Y-1,
    Z1 #= Z-1,
%    solve([X,Y,X1,Y1,Z1]),
    checksat,
    tak(X1, Y,   Z,  A1),
    tak(Y1, Z,   X,  A2),
    tak(Z1, X,   Y,  A3),
    tak(A1,  A2,  A3, A ).

% :- use_package(clpq).
% :- export(takp/4).
% %takp(X, Y, Z, A) :-
% %    display(tak(X, Y, Z, A)), nl, fail.
% takp(X, Y, Z, A) :-
%     X .=<. Y,
%     Z = A.
% takp(X, Y, Z, A) :-
%     X .>=. Y+1,
%     X1 .=. X-1,
%     Y1 .=. Y-1,
%     Z1 .=. Z-1,
%     takp(X1, Y,   Z,  A1),
%     takp(Y1, Z,   X,  A2),
%     takp(Z1, X,   Y,  A3),
%     takp(A1,  A2,  A3, A ).
