%
% Matrixlog: Programming with Matrices and Logic
%
% Authors:
%     James Johnson
%     Jerry Yin
%

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

% Matrix is a valid matrix.
valid_matrix(Matrix) :-
  Matrix = matrix(M, N, Elements),
  M #> 0, N #> 0,
  Size #= M * N,
  functor(Elements, elements, Size),
  Elements =.. [_FunctorName | LElm],
  maplist(number, LElm).

% True iff the value of matrix M at row I, column J is V.
at(matrix(M, N, Elements), I, J, V) :-
  I #> 0, I #=< M,
  J #> 0, J #=< N,
  Size #= M * N,
  functor(Elements, elements, Size),
  Index #= (I - 1) * N + J,
  arg(Index, Elements, V).

% True iff Matrix is an M x N matrix of all ones.
ones(M, N, Matrix) :-
  Size #= M * N,
  functor(Elements, elements, Size),
  foreach(between(1, Size, I), arg(I, Elements, 1)),
  Matrix = matrix(M, N, Elements).

% True iff Matrix is an M x N matrix of all zeros.
zeros(M, N, Matrix) :-
  Size #= M * N,
  functor(Elements, elements, Size),
  foreach(between(1, Size, I), arg(I, Elements, 0)),
  Matrix = matrix(M, N, Elements).

% True iff Matrix is an N x N identity matrix.
eye(N, Matrix) :-
  Size #= N * N,
  functor(Elements, elements, Size),
  foreach((between(1, N, I), between(1, N, J), Index #= I + (J - 1) * N),
          I = J -> arg(Index, Elements, 1) ; arg(Index, Elements, 0)),
  Matrix = matrix(N, N, Elements).

% T is the transpose of A.  In other words, T is A but with row and column
% indices switched.
t(_A, _T) :-
  throw(todo). % TODO:

% R is the matrix sum of A and B.
add(_A, _B, _R) :-
  throw(todo). % TODO:

% Row is a list representing row I of Matrix.
row(Matrix, I, Row) :-
  Matrix = matrix(M, N, Elements),
  I #=< M, I #> 0,
  functor(Elements, elements, _Size),
  Start #= (I - 1) * N + 1, % start of slice
  End #= (I - 1) * N + N, % end of slice
  findall(Value, (between(Start, End, Index), arg(Index, Elements, Value)), Row).

% Col is a list representing column J of Matrix.
column(Matrix, J, Col) :-
  Matrix = matrix(M, N, Elements),
  J #=< N, J #> 0,
  functor(Elements, elements, _Size),
  findall(Value,
          (I in 1..M, Index #= (I - 1) * N + J, arg(Index, Elements, Value)),
          Col).

% dot(X, Y, R) is true if R is the dot product of the lists X and Y.
dot([], [], 0).
dot([X | XTl], [Y | YTl], R) :-
  dot(XTl, YTl, Acc),
  R is X * Y + Acc.

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

%! forsub(+L, -X, +B)
%
% Given that L is a lower triangular matrix, forsub(L, X, B) is true if the
% linear system L * X = B holds.
%
% A *lower triangular matrix* is a matrix where all entries above the main
% diagonal are zero.
forsub(_L, _X, _B) :-
  throw(todo). % TODO:

%! backsub(+U, -X, +B)
%
% Given that U is an upper triangular matrix, backsub(U, X, B) is true if the
% linear system U * X = B holds.
%
% An *upper triangular matrix* is a matrix where all entries below the main
% diagonal are zero.
backsub(_U, _X, _B) :-
  throw(todo). % TODO:


%%%%%%%%%
% Tests %
%%%%%%%%%

:- begin_tests(matrixlog).

test(valid_matrix) :-
  assertion(valid_matrix(matrix(1, 1, elements(42)))),
  assertion(valid_matrix(matrix(2, 2, elements(1, 0, 0, 1)))),
  assertion(valid_matrix(matrix(3, 1, elements(1.0, 2.0, 3.0)))).
test(invalid_matrix) :-
  assertion(not(valid_matrix(matrix(0, 0, elements())))),
  assertion(not(valid_matrix(matrix(3, 1, elms(1.0, 2.0, 3.0))))),
  assertion(not(valid_matrix(matrix(3, 1, elms(1, 2))))).
test(invalid_variable_matrix) :-
  assertion(not(valid_matrix(matrix(1, 1, elms(_))))). % since it's not provable

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

:- end_tests(matrixlog).
