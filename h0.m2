needs "S.m2" -- n and p are defined.

-- Computes a basis for K(d,e) of eigenvectors for the torus.
-- WARNING: Indexing in this program does not match the paper.
-- K(d,e) of the old code is K(d,e+1) of the paper, which is 
-- H^1(e+1,d) in Gao-Raicu 2024.
K = method(Options => {Verbose => true})
K(ZZ,ZZ) := opts -> (d, e) -> (
  if opts.Verbose then
    print concatenate("Computing K(", toString(d), ",",
      toString(e), ")");
  matp := contract(transpose basis(d-1, Sp),basis(d, Sp));
  Mp := ker(matp**Sp^{d});
  basisE := ambient(basis(e-1, Mp));
  basisD := basis(d, Sp);
  
  found := new MutableHashTable;
  for i in 0..numcols(basisE)-1 do (
    vec = basisE_i;
    weight := first exponents(
      for j from 0 to rank class vec - 1 do (
        if vec_j == 0 then continue;
        ans := basisD_(0,j) * vec_j;
        if ans != 0 then break ans
      )
    );
    assert(sum(weight) == d + e - 1);
    kerElt := sum entries vec;
    if found#?weight then
      found#weight = found#weight | {kerElt}
    else
      found#weight = {kerElt}
  );
  found
)

-- Computes the character kappa(d,e).
kappa = method()
kappa(ZZ,ZZ) := (d, e) -> contents K(d,e)

-- Displays various aspects of K(d,e).
testK = method()
testK(ZZ,ZZ) := (d, e) -> toCharacter K(d,e)

-- Maximum d giving a nonzero K(d,e) for a given e, as proved in Gao-Raicu
-- 2024, Theorem 1.1.
max'd = method()
max'd(ZZ) := e -> (
  k = floorLog(p,e);
  t = floor(e / p^k);
  (t + n - 2)*p^k - n + 1
)

-- Displays various aspects of K(d,e) for a range of d and e.
allK = method(Dispatch => Thing, Options => {emax => 30})
allK(Sequence) := opts -> () ->
  for e in 1..opts.emax do
    for d in e..max'd(e) do
      testK(d, e);

allKappa = method(Dispatch => Thing, Options => {emax => 30})
allKappa(Sequence) := opts -> () ->
  for e in 1..opts.emax do
    for d in e..max'd(e) do
      print graph kappa(d, e);

-- Displays kappa(d,e) for a range of d and e, displayed as a linear combination
-- of matrices with integer coefficients, each A standing for MS[A].
allMS = method(Dispatch => Thing, Options => {emax => 30})
allMS(Sequence) := opts -> () ->
  for e in 1..opts.emax do
    for d in e..max'd(e) do (
      print (d, e);
      print toDigMats MSdecomp toCharacter(
        K(d, e, Verbose => false), Silent => true
      )
    )

-- Helper methods for h0b and H0b (see below)
boxIdeal = method(Dispatch => Thing);
boxIdeal(Sequence) :=
boxIdeal(List)     := ww -> (
  if #ww != n then error(ww);
  ideal(for i in 1..n list z_i^(ww_(i - 1) + 1))
)

box = method(Dispatch => Thing);
box(Sequence) :=
box(List)     := ww -> (Sp^1/boxIdeal(ww))


h0b = method()
h0b(ZZ,ZZ,List) := (d,e,ww) -> (
  if #ww != n then error ww;
  if sum ww != d + e - 1 then error ww;
  b = box(ww);
  m = map(b, b, omega);
  hilbertFunction(e - 1, kernel m)
)

H0b = method()
H0b(ZZ,ZZ,List) := (d,e,ww) -> (
  if #ww != n then error ww;
  if sum ww != d + e - 1 then error ww;
  b = box(ww);
  m = map(b, b, omega);
  first entries super basis(e - 1, kernel m)
)

dispH0b = method()
dispH0b(ZZ,ZZ,List) := (d,e,ww) -> (
  for elt in H0b(d,e,ww) do (
    print graph plift (elt * (leadCoefficient elt)^-1);
    print "";
  )
)

-- Computes the dimensions of K(d,e) for a square range of d and e.
h0Matrix = method(Dispatch => Thing, Options => {dmax => 10})
h0Matrix(Sequence) := opts -> () -> (
  netList for e in 1..opts.dmax list for d in 0..opts.dmax list #K(d,e)
)

-- Sum of K-spaces along diagonal line, following Han-Monsky paper
hanMonskySum = method()
hanMonskySum(ZZ) := s -> (
  sum for d in 0..s list contents K(d,s-d)
)

hanMonskySumAll = method(Dispatch => Thing, Options => {imax => 30})
hanMonskySumAll(Sequence) := opts -> () -> (
  for i from 1 to opts.imax do (
     << "i = " << i << endl;
     << graph(hanMonskySum(i) * SchurDenom) -- to separate the Schur summands
  )
)