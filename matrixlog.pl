%
% Matrixlog: Programming with Matrices and Logic
%
% Authors:
%     James Johnson
%     Jerry Yin
%

:- module(matrixlog,
          [valid_matrix/1, at/4, ones/3, zeros/3, eye/2, t/2, add/3,
           ms_product/3, multiply/3, lu/3, solve/3, close/3]).

:- use_module(library(clpfd)).

% We represent a matrix as
%
%     matrix(M = NumRows, N = NumCols,
%            elements(E11, E12, ..., E1N,
%                     E21, E22, ..., E2N,
%                     ⋮    ⋮    ⋱    ⋮
%                     EM1, EM2, ..., EMN))
%
% The elements are stored in row-major order -- entries from the same row
% are "close together".

%! valid_matrix(+Matrix)
%
% Matrix is a valid matrix.
valid_matrix(matrix(M, N, Elements)) :-
  M #> 0, N #> 0,
  Size #= M * N,
  functor(Elements, elements, Size),
  Elements =.. [_FunctorName | LElm],
  maplist(number, LElm).


%! at(+Matrix, ?I, ?J, ?V)
%
% The value of the matrix Matrix at row I, column J is V.
at(matrix(M, N, Elements), I, J, V) :-
  I #> 0, I #=< M,
  J #> 0, J #=< N,
  Size #= M * N,
  functor(Elements, elements, Size),
  Index #= (I - 1) * N + J,
  arg(Index, Elements, V).


%! ones(+M, +N, ?Matrix)
%
% Matrix is an M x N matrix of all ones.
ones(M, N, Matrix) :-
  Size #= M * N,
  functor(Elements, elements, Size),
  foreach(between(1, Size, I), arg(I, Elements, 1)),
  Matrix = matrix(M, N, Elements).


%! zeros(+M, +N, ?Matrix)
%
% Matrix is an M x N matrix of all zeros.
zeros(M, N, Matrix) :-
  Size #= M * N,
  functor(Elements, elements, Size),
  foreach(between(1, Size, I), arg(I, Elements, 0)),
  Matrix = matrix(M, N, Elements).


%! eye(+N, ?Matrix)
%
% Matrix is an N x N identity matrix.
eye(N, Matrix) :-
  Size #= N * N,
  functor(Elements, elements, Size),
  foreach((between(1, N, I), between(1, N, J), Index #= I + (J - 1) * N),
          I = J -> arg(Index, Elements, 1) ; arg(Index, Elements, 0)),
  Matrix = matrix(N, N, Elements).


%! t(+A, ?T)
%
% T is the transpose of A.  In other words, T is A but with row and column
% indices switched.
t(A,T) :-
  A = matrix(M,N,Elements),
  Size #= M*N,
  functor(Elements,elements,Size),
  functor(Telements,elements,Size),
  foreach((between(1,M,I),
           between(1,N,J),
           Index #= J + (I-1)*N,
           arg(Index,Elements,V),
           Tindex #= I + (J-1)*M),
          arg(Tindex,Telements,V)),
  T = matrix(N,M,Telements).


%! add(+A, +B, ?R)
%
% R is the matrix sum of A and B.
add(A, B, R) :-
  A = matrix(M,N,AElements),
  B = matrix(M,N,BElements),
  Size #= M*N,
  functor(AElements,elements,Size),
  functor(BElements,elements,Size),
  functor(ResElements,elements,Size),
  AElements =.. [elements|As],
  BElements =.. [elements|Bs],
  maplist(add_el,As,Bs,Res),
  ResElements =.. [elements|Res],
  R = matrix(M,N,ResElements).

add_el(A,B,C):- C is A + B.


%! row(+Matrix, +I, ?Row)
%
% Row is a list representing row I of Matrix.
row(Matrix, I, Row) :-
  Matrix = matrix(M, N, Elements),
  I #=< M, I #> 0,
  functor(Elements, elements, _Size),
  Start #= (I - 1) * N + 1, % start of slice
  End #= (I - 1) * N + N, % end of slice
  findall(Value, (between(Start, End, Index), arg(Index, Elements, Value)), Row).


%! col(+Matrix, +J, ?Col)
%
% Col is a list representing column J of Matrix.
column(Matrix, J, Col) :-
  Matrix = matrix(M, N, Elements),
  J #=< N, J #> 0,
  functor(Elements, elements, _Size),
  findall(Value,
          (I in 1..M, Index #= (I - 1) * N + J, arg(Index, Elements, Value)),
          Col).


%! dot(+X, +Y, ?R)
%
% R is the dot product of the lists X and Y.
dot([], [], 0).
dot([X | XTl], [Y | YTl], R) :-
  dot(XTl, YTl, Acc),
  R is X * Y + Acc.


%! ms_product(+A, +X, ?R)
%
% R is the result of matrix-scalar product X * A, where X is a scalar and A is
% a matrix.
ms_product(A, X, R) :-
  number(X),
  A = matrix(M, N, As),
  R = matrix(M, N, Rs),
  Size #= M * N,
  functor(As, elements, Size),
  functor(Rs, elements, Size),
  foreach((arg(I, As, Value), ScaledValue is X * Value),
          arg(I, Rs, ScaledValue)).


%! multiply(+A, +B, ?R)
%
% R is the result of matrix product A * B.
multiply(A, B, R) :-
  A = matrix(M, S, _),
  B = matrix(S, N, _),
  R = matrix(M, N, Rs),
  Size #= M * N,
  functor(Rs, elements, Size),
  foreach((between(1, M, I), between(1, N, J), Index #= J + (I - 1) * N,
           row(A, I, Row), column(B, J, Col), dot(Row, Col, Value)),
          arg(Index, Rs, Value)).


%! forsub(+L, ?X, +B)
%
% L should be a lower triangular matrix.  forsub(L, X, B) is true if the linear
% system L * X = B holds.
%
% A *lower triangular matrix* is a matrix where all entries above the main
% diagonal are zero.
forsub(L, X, matrix(N, 1, Belems)) :-
  L = matrix(N,N,Lower),
  Size #= N*N,
  functor(Lower,elements,Size),
  functor(Belems,elements,N),
  Belems =.. [elements|Bs],
  subrec(Lower,N,Bs,Xs),
  Xelems =.. [elements|Xs],
  X = matrix(N,1,Xelems).

% Actual work of forward substitution
% Ts is a row-major list of the elements of N x N lower triangular matrix T
% T * X = B
subrec(Ts,N,[B1|Bs],Xs) :-
  arg(1,Ts,T_11),
  T_11 =\= 0,
  X_1 is B1 / T_11,
  subrec(Ts, N, 2, Bs, [X_1], Xs).

subrec(_Ts, _N, _I, [],       Xs,  Xs) :- !. % ! means to stop looking for more
                                             % answers
subrec(Ts,  N,  I,  [B_i|Bs], Acc, Xs) :-
  DiagIndex #= I + (I - 1) * N,
  TStart #= 1 + (I - 1) * N,
  TStop #= DiagIndex - 1,
  % Get all coefficients that are going to be multiplied by known values
  % (T[i,1] through T[i,i-1])
  findall(Value, (between(TStart, TStop, Index), arg(Index, Ts, Value)), Trow),
  % Substitute all known values and multiply by coefficients in row
  dot(Trow, Acc, Summand),
  % Summand + T[i,i] * X[i] == B[i]
  arg(DiagIndex, Ts, T_ii),
  X_i is (B_i - Summand) / T_ii,
  append(Acc, [X_i | _], Xs),
  append(Acc, [X_i], Next),
  IPlus1 #= I + 1,
  subrec(Ts, N, IPlus1, Bs, Next, Xs).


%! backsub(+U, ?X, +B)
%
% U should be an upper triangular matrix.  backsub(U, X, B) is true if the
% linear system U * X = B holds.
%
% An *upper triangular matrix* is a matrix where all entries below the main
% diagonal are zero.
backsub(U, X, matrix(N, 1, Belems)) :-
  U = matrix(N,N,Upper),
  Size #= N*N,
  functor(Upper,elements,Size),
  functor(Belems,elements,N),
  Belems =.. [elements|Bs],
  reverse(Bs,RBs),
  Upper =.. [elements|Us],
  reverse(Us,RUs),
  RUpper =.. [elements|RUs],
  % we express backsub in terms of a forward substitution
  subrec(RUpper,N,RBs,RXs),
  reverse(RXs,Xs),
  Xelems =.. [elements|Xs],
  X = matrix(N,1,Xelems).


%! lu(+A, -L, -U)
%
% A can be decomposed into L * U such that L is lower-triangular and U is
% upper-triangular.
%
% Uses Doolittle's method.
lu(A,L,U) :-
  A = matrix(N,N,AElements),
  Size #= N*N,
  functor(AElements,elements,Size),
  functor(LElements,elements,Size),
  functor(UElements,elements,Size),
  lu_row(0, N, AElements, LElements, UElements),
  L = matrix(N, N, LElements),
  U = matrix(N, N, UElements).

% Compute a single row of Lower and Upper.
lu_row(N, N, _As, _Ls,   _Us) :- !.
lu_row(J, N, As,  Lower, Upper) :-
  Jplus #= J + 1,
  IndexJJ #= Jplus + J * N,
  setarg(IndexJJ, Lower, 1), % set L[Jplus,Jplus] = 1
  lu_element(0,Jplus,N,As,Lower,Upper),
  lu_row(Jplus,N,As,Lower,Upper).

% Compute a single element of Lower and Upper.
lu_element(N, _J, N, _As, _Ls,   _Us) :- !.
lu_element(I, J,  N, As,  Lower, Upper) :-
  Iplus #= I + 1,
  Index #= J + I * N,
  arg(Index,As,Av),
  % If I < J...
  (I < J ->
     % Compute the value of U[Iplus, J]
     (sum_l_ik_u_kj(Iplus,Iplus,J,N,Lower,Upper,Sum),
      ValUpper is Av - Sum,
      setarg(Index,Upper,ValUpper),
      % Zero out the corresponding value of L if necessary
      % We've already set the diagonals to 1 in lu_row, so we skip that case
      (Iplus < J ->
         setarg(Index,Lower,0);
         true));
     % Otherwise, compute the value of Lower[Iplus, J]
     (sum_l_ik_u_kj(J,Iplus,J,N,Lower,Upper,Sum),
      JJ #= J+(J-1)*N,
      arg(JJ,Upper,Ujj),
      ValLower is (Av-Sum)/Ujj,
      setarg(Index,Lower,ValLower),
      % and zero out the corresponding value of L
      setarg(Index,Upper,0))),
  lu_element(Iplus,J,N,As,Lower,Upper).

% Computes sum of Lower[I, K] * Upper[K, J] for K = 1..Stop-1
sum_l_ik_u_kj(Stop,I,J,N,Lower,Upper,Sum) :-
  sum_l_ik_u_kj(1,Stop,I,J,N,Lower,Upper,0,Sum).

sum_l_ik_u_kj(K, K,    _I, _J, _N, _Lower, _Upper, Sum, Sum) :- !.
sum_l_ik_u_kj(K, Stop, I,  J,  N,  Lower,  Upper,  Acc, Sum) :-
  Kplus #= K + 1,
  LIdx #= K+(I-1)*N,
  UIdx #= J+(K-1)*N,
  arg(LIdx,Lower,Lv), % Lv = L[I, K]
  arg(UIdx,Upper,Uv), % Uv = U[K, J]
  NextAcc is Acc + (Lv*Uv),
  sum_l_ik_u_kj(Kplus,Stop,I,J,N,Lower,Upper,NextAcc,Sum).


%! solve(+A, ?X, +B)
%
% Attempts to solve A * X = B, by using LU factorization of A, where B is a
% column vector and A is square.
%
% forward substitution on LF = B, backwards substitution on UX = F
solve(A,X,B) :-
  A = matrix(N, N, As),
  B = matrix(N, 1, Bs),
  SizeA #= N*N,
  functor(As, elements, SizeA),
  functor(Bs, elements, N),
  lu(A, L, U),
  forsub(L, F, B),
  backsub(U, X, F).


%! close(+A, +B, +Epsilon)
%
% Each element of matrices A and B differs by no more than Epsilon.
close(matrix(M, N, AElems), matrix(M, N, BElems), Epsilon) :-
  Size #= M * N,
  foreach((between(1, Size, I),
           arg(I, AElems, ValA),
           arg(I, BElems, ValB),
           Diff is abs(ValA - ValB)),
          Diff =< Epsilon).


%%%%%%%%%
% Tests %
%%%%%%%%%

:- begin_tests(test_matrixlog).

test(valid_matrix) :-
  assertion(valid_matrix(matrix(1, 1, elements(42)))),
  assertion(valid_matrix(matrix(2, 2, elements(1, 0, 0, 1)))),
  assertion(valid_matrix(matrix(3, 1, elements(1.0, 2.0, 3.0)))).
test(invalid_matrix) :-
  assertion(not(valid_matrix(matrix(0, 0, elements())))),
  assertion(not(valid_matrix(matrix(3, 1, elms(1.0, 2.0, 3.0))))),
  assertion(not(valid_matrix(matrix(3, 1, elms(1, 2))))).
test(invalid_variable_matrix) :-
  assertion(not(valid_matrix(matrix(1, 1, elms(_))))). % since it is not provable

test(at) :-
  at(matrix(2, 2, elements(10, 20, 30, 40)), 1, 1, R),
  assertion(R =:= 10).
test(at) :-
  assertion(at(matrix(2, 2, elements(10, 20, 30, 40)), 1, 1, 10)),
  assertion(at(matrix(2, 2, elements(10, 20, 30, 40)), 1, 2, 20)),
  assertion(at(matrix(2, 2, elements(10, 20, 30, 40)), 2, 1, 30)),
  assertion(at(matrix(2, 2, elements(10, 20, 30, 40)), 2, 2, 40)).
test(at) :-
  assertion(at(matrix(2, 3, elements(11, 12, 13, 21, 22, 23)), 2, 3, 23)),
  assertion(at(matrix(2, 3, elements(11, 12, 13, 21, 22, 23)), 1, 2, 12)).
test(at, [nondet]) :-
  at(matrix(2, 2, elements(1, 2, 3, 4)), I, J, 2),
  assertion(I =:= 1),
  assertion(J =:= 2).
test(at_float) :-
  assertion(at(matrix(2, 3, elements(0.1, 0.2, 0.3, 0.4, 0.5, 0.6)), 2, 2,
               0.5)).

test(guess_dims) :-
  findall((M, N), at(matrix(M, N, elements(1, 2, 3, 4)), 2, 1, _), Results),
  assertion(Results == [(4, 1), (2, 2)]).

test(ones) :-
  ones(2, 2, R),
  assertion(R == matrix(2, 2, elements(1, 1, 1, 1))).
test(ones) :- assertion(ones(1, 1, matrix(1, 1, elements(1)))).
test(ones) :- assertion(ones(3, 1, matrix(3, 1, elements(1, 1, 1)))).

test(zeros) :-
  zeros(2, 2, R),
  assertion(R == matrix(2, 2, elements(0, 0, 0, 0))).
test(zeros) :- assertion(zeros(1, 1, matrix(1, 1, elements(0)))).
test(zeros) :- assertion(zeros(3, 1, matrix(3, 1, elements(0, 0, 0)))).

test(eye) :-
  eye(2, R),
  assertion(R == matrix(2, 2, elements(1, 0, 0, 1))).
test(eye) :- assertion(eye(1, matrix(1, 1, elements(1)))).
test(eye) :-
  assertion(eye(3, matrix(3, 3, elements(1, 0, 0, 0, 1, 0, 0, 0, 1)))).

test(at_eye) :-
  eye(2, Ident),
  findall((I, J), at(Ident, I, J, 1), Results),
  assertion(Results == [(1, 1), (2, 2)]).

test(matrix_scalar_product_integer) :-
  ms_product(matrix(2, 2, elements(4, 3, 2, 1)), 3, R),
  assertion(R == matrix(2, 2, elements(12, 9, 6, 3))).
test(matrix_scalar_product_integer) :-
  assertion(ms_product(matrix(2, 2, elements(4, 3, 2, 1)), 3,
                       matrix(2, 2, elements(12, 9, 6, 3)))),
  assertion(ms_product(matrix(2, 1, elements(4, 3)), 0,
                       matrix(2, 1, elements(0, 0)))).
test(matrix_scalar_product_mixed) :-
  assertion(ms_product(matrix(2, 2, elements(4, 3, 2, 1)), 0.5,
                       matrix(2, 2, elements(2.0, 1.5, 1.0, 0.5)))),
  assertion(ms_product(matrix(3, 2, elements(0.1, 0.2, 0.3, 0.4, 0.5, 0.6)), 10,
                       matrix(3, 2, elements(1.0, 2.0, 3.0, 4.0, 5.0, 6.0)))).
test(matrix_scalar_product_float) :-
  assertion(ms_product(matrix(2, 2, elements(0.0, 1.0, 2.0, 3.0)), 0.5,
                       matrix(2, 2, elements(0.0, 0.5, 1.0, 1.5)))),
  assertion(ms_product(matrix(1, 1, elements(123.4567)), 3.141,
                       matrix(1, 1, elements(387.7774947)))).

test(dot) :-
  dot([23.4], [2], R),
  assertion(R =:= 46.8).
test(dot) :-
  assertion(dot([], [], 0)),
  assertion(dot([23.4], [2], 46.8)),
  assertion(dot([0.1], [10.0], 1.0)),
  assertion(dot([1, 2, 3], [4, 5, 6], 32)).
test(dot_fail) :-
  assertion(not(dot([1, 2], [3, 4, 5], _))).

test(row) :-
  row(matrix(2, 2, elements(1, 2, 3, 4)), 1, R),
  assertion(R == [1, 2]).
test(row) :-
  assertion(row(matrix(2, 2, elements(1, 2, 3, 4)), 1, [1, 2])),
  assertion(row(matrix(2, 2, elements(1, 2, 3, 4)), 2, [3, 4])),
  assertion(row(matrix(2, 3, elements(11, 22, 33, 44, 55, 66)), 2,
                [44, 55, 66])),
  assertion(row(matrix(3, 1, elements(1.01, 2.02, 3.03)), 2, [2.02])).

test(column) :-
  column(matrix(2, 2, elements(1, 2, 3, 4)), 1, C),
  assertion(C == [1, 3]).
test(column) :-
  assertion(column(matrix(2, 2, elements(1, 2, 3, 4)), 1, [1, 3])),
  assertion(column(matrix(2, 2, elements(1, 2, 3, 4)), 2, [2, 4])),
  assertion(column(matrix(3, 2, elements(11, 22, 33, 44, 55, 66)), 2,
                   [22, 44, 66])),
  assertion(column(matrix(3, 1, elements(1.01, 2.02, 3.03)), 1,
                   [1.01, 2.02, 3.03])),
  assertion(column(matrix(1, 3, elements(1.01, 2.02, 3.03)), 1, [1.01])).

test(multiply_integer) :-
  multiply(matrix(1, 1, elements(2)), matrix(1, 1, elements(-7)), R),
  assertion(R == matrix(1, 1, elements(-14))).
test(multiply_integer) :-
  multiply(matrix(1, 3, elements(1, -1, 1)), matrix(3, 1, elements(4, 9, 8)), R),
  assertion(R == matrix(1, 1, elements(3))).
test(multiply_integer) :-
  multiply(matrix(2, 1, elements(1, 2)), matrix(1, 2, elements(3, 4)), R),
  assertion(R == matrix(2, 2, elements(3, 4, 6, 8))).
test(multiply_integer) :-
  eye(2, I2),
  assertion(multiply(I2, matrix(2, 2, elements(1, -2, -3, 4)),
                     matrix(2, 2, elements(1, -2, -3, 4)))),
  assertion(multiply(matrix(2, 2, elements(1, -2, -3, 4)), I2,
                     matrix(2, 2, elements(1, -2, -3, 4)))).
test(multiply_integer) :-
  multiply(matrix(2, 3, elements(1, 2, 3, 4, 5, 6)),
           matrix(3, 2, elements(-1, 1, 2, -4, -9, -20)), R),
  assertion(R == matrix(2, 2, elements(-24, -67, -48, -136))).

test(t) :-
  A = matrix(1, 1, elements(1)),
  t(A, T),
  assertion(T = matrix(1, 1, elements(1))).
test(t) :-
  A = matrix(2, 2, elements(1.0, 2.0, 3.0, 4.0)),
  t(A, T),
  assertion(T = matrix(2, 2, elements(1.0, 3.0, 2.0, 4.0))).
test(t) :-
  t(matrix(2, 3,elements(1, 2, 3, 4, 5, 6)), T),
  assertion(T = matrix(3, 2, elements(1, 4, 2, 5, 3, 6))).

test(add) :-
  ones(3,3,One),
  eye(3,Id),
  ms_product(Id,2,Two),
  add(One,Two,matrix(3,3,elements(3,1,1,1,3,1,1,1,3))).

test(add) :-
  add(matrix(2,2,elements(0.0345,0,0,2.5432)),
      matrix(2,2,elements(0.9655,2.0,3.0,1.4568)),
      R),
  assertion(R == matrix(2,2,elements(1.0,2.0,3.0,4.0))).

test(forsub) :-
  forsub(matrix(1, 1, elements(4)), X, matrix(1, 1, elements(-2))),
  assertion(X == matrix(1, 1, elements(-0.5))).
test(forsub) :-
  eye(3, A),
  B = matrix(3,1,elements(1.0,2.0,3.0)),
  forsub(A,X,B),
  assertion(X = matrix(3,1,elements(1.0,2.0,3.0))).
test(forsub) :-
  forsub(matrix(3,3,elements(1.0,0,0,2.0,3.0,0,4.0,5.0,6.0)),
         matrix(3,1,elements(3.0,-1.0,-1.0)),
         matrix(3,1,elements(3.0,3.0,1.0))).
test(forsub) :-
  assertion(not(forsub(matrix(3,3,elements(1.0,0,0,2.0,3.0,0,4.0,5.0,6.0)),
                       matrix(3,1,elements(-1.0,3.0,3.0)),
                       matrix(3,1,elements(3.0,3.0,1.0))))).

test(backsub) :-
  forsub(matrix(1, 1, elements(4)), X, matrix(1, 1, elements(-2))),
  assertion(X == matrix(1, 1, elements(-0.5))).
test(backsub) :-
  A = matrix(3,3,elements(1,0,0,0,1,0,0,0,1)),
  B = matrix(3,1,elements(1.0,2.0,3.0)),
  backsub(A,X,B),
  assertion(X = matrix(3,1,elements(1.0,2.0,3.0))).
test(backsub) :-
  backsub(matrix(3,3,elements(6,5,4,0,3,2,0,0,1)),
          matrix(3,1,elements(-2.0,-2.0,6.0)),
          matrix(3,1,elements(2.0,6.0,6.0))).
test(backsub) :-
  assertion(not(backsub(matrix(3,3,elements(6,5,4,0,3,2,0,0,1)),
                        matrix(3,1,elements(-1.0,3.0,3.0)),
                        matrix(3,1,elements(3.0,3.0,1.0))))).

test(backsub_nosol) :-
  assertion(not(backsub(matrix(2, 2, elements(0, 1, 0, 0)), _X,
                        matrix(2, 1, elements(3, 4))))).
test(backsub_nosol) :-
  assertion(not(backsub(matrix(2, 2, elements(0.0, 1.0, 0.0, 0.0)), _X,
                        matrix(2, 1, elements(3.0, 4.0))))).

test(forsub_nosol) :-
  assertion(not(forsub(matrix(2, 2, elements(0, 0, 1, 0)), _X,
                       matrix(2, 1, elements(3, 4))))).
test(forsub_nosol) :-
  assertion(not(forsub(matrix(2, 2, elements(0.0, 0.0, 1.0, 0.0)), _X,
                       matrix(2, 1, elements(3.0, 4.0))))).

test(lu) :-
  A = matrix(3,3,elements(1,0,0,0,2,0,0,0,3)),
  lu(A,L,U),
  assertion(U = matrix(3, 3, elements(1,0,0,0,2,0,0,0,3))),
  assertion(L = matrix(3, 3, elements(1,0,0,0,1,0,0,0,1))),
  assertion(multiply(L, U, A)).
test(lu) :-
  A = matrix(3,3,elements(1,2,0,2,7,0,0,0,1)),
  lu(A,L,U),
  assertion(U = matrix(3, 3, elements(1,2,0,0,3,0,0,0,1))),
  assertion(L = matrix(3, 3, elements(1,0,0,2,1,0,0,0,1))),
  assertion(multiply(L, U, A)).

test(lu_float) :-
  A = matrix(4, 4, elements(0.9, 0.0, 0.1, 0.3,
                            0.7, 0.3, 0.5, 0.9,
                            0.3, 0.1, 0.7, 0.2,
                            0.9, 0.1, 0.7, 0.3)),
  lu(A, L, U),
  multiply(L, U, AReconstructed),
  assertion(close(A, AReconstructed, 1e-8)).

test(solve_integer) :-
  solve(matrix(1,1,elements(1)),
        matrix(1,1,elements(2)),
        matrix(1,1,elements(2))).
test(solve_integer) :-
  A = matrix(2,2,elements(2,0,0,2)),
  B = matrix(2,1,elements(2,4)),
  solve(A,X,B),
  assertion(X = matrix(2,1,elements(1,2))).
test(solve_integer) :-
  A = matrix(2,2,elements(2,0,0,2)),
  B = matrix(2,1,elements(2,4)),
  solve(A,X,B),
  assertion(X = matrix(2,1,elements(1,2))).

test(solve_float) :-
  solve(matrix(2, 2, elements(1.0, 0.0, 0.0, 1.0)), X,
        matrix(2, 1, elements(3.0, -1.2))),
  assertion(X == matrix(2, 1, elements(3.0, -1.2))).

test(solve_nosol) :-
  assertion(not(solve(matrix(2, 2, elements(1.0, 0.0, 0.0, 1.0)), _X,
                      matrix(3, 1, elements(3.0, -1.2, -4.44, 8.0))))).

error(zero_divisor) :-
  lu(matrix(2,2,elements(0,1,1,0)),L,U),
  valid_matrix(L),
  valid_matrix(U).
error(zero_divisor) :-
  solve(matrix(2,2,elements(0,1,1,0)),
        matrix(2,1,elements(2,1)),
        matrix(2,1,elements(1,2))).

:- end_tests(test_matrixlog).
