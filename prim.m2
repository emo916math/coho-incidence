needs "h0.m2"


-- Note: "pocket" is a term that didn't make it into the paper.
-- A pocket is a ((d0,e0),k) such that applying Frob^k to K(d0,e0) lands you
-- in a bidegree that can contribute to K(d1,e1).
getPocket = method(Options => {Verbose => true})
getPocket(Sequence,Sequence,ZZ) := opts -> (de0, de1, k) -> (
  (d0,e0) := de0;
  (d1,e1) := de1;
  h := Kprim(d0, e0, Verbose => false);
    -- recursively till there are no pockets in range
  en := e1 - p^k*e0;
  vs := tuplesWithSum(n, en);
  dn := (n-1)*(p^k - 1) + p^k*d0 - d1;
  usLong := tuplesWithSum(n, dn);
  usShort := for l in tuplesWithSum(n - 1, dn) list {0} | l;
  found := new MutableHashTable;
  if opts.Verbose then
    << "Computing pocket " << (de0, de1, k) << endl;
  for entry in pairs h do (
    (weight0, kerElts0) := entry;
    for kerElt0 in kerElts0 do (
      for v in vs do (
        us := if first v == 0 then usLong else usShort;
        -- us := usLong;
        for u in us do (
          newWt := p^k * weight0 + toList(n:p^k-1) + v - u;
          if min(newWt) < 0 then continue;
          I := boxIdeal(newWt);
          newKerElt1 := (Frobpk k) kerElt0 * omega^(p^k - 1) * zmon v;
          newKerElt := newKerElt1 % I;
          if found#?newWt then
            found#newWt = found#newWt | {newKerElt}
          else
            found#newWt = {newKerElt}
        )
      )
    )
  );
  if opts.Verbose then
    print("Found " | #found | " weights");
  found
);

-- One entry of a pocket.
getPocket(Sequence,Sequence,ZZ,List) := opts -> (de0, de1, k, ww) -> (
  (d0,e0) := de0;
  (d1,e1) := de1;
  h := Kprim(d0, e0, Verbose => false);
  en := e1 - p^k*e0;
  vs := tuplesWithSum(n, en);
  dn := (n-1)*(p^k - 1) + p^k*d0 - d1;
  I := boxIdeal(ww);
  found := {};
  if opts.Verbose then (
    << "Computing pocket " << (de0, de1, k) << " in weight " << ww
    << "... " << flush
  );
  for entry in pairs h do (
    (weight0, kerElts0) := entry;
    for v in vs do (
      u := p^k * weight0 + toList(n:p^k-1) + v - ww;
      if min u < 0 then continue;
      if u_0 > 0 and v_0 > 0 then continue;
      for kerElt0 in kerElts0 do (
        newKerElt1 := (Frobpk k) kerElt0 * omega^(p^k - 1) * zmon v;
        newKerElt := newKerElt1 % I;
        if newKerElt != 0 then 
          found = found | {newKerElt}
      )
    )
  );
  if opts.Verbose then
    print("Found " | #found | " in pocket");
  found
);

-- Four versions of the pocketIndices method, to compute generators of K
-- in different senses.

pocketIndices1 = method()
pocketIndices1(ZZ,ZZ) := (d1, e1) -> (
  (flatten for k from 1 to floorLog(p, e1) list (
    maxM = floor(e1/p^k);
    minM = max(1, 1 + ceiling((d1 - (n-1)*(p^k - 1))/p^k));
    for m from minM to maxM list ((m-1, m), k)
  )) 
)

-- Shoreline pockets ((m-1,m), 0) only:
pocketIndicesL = method()
pocketIndicesL(ZZ,ZZ) := (d1, e1) -> (
  if d1 < e1 then for m from d1+1 to e1 list ((m-1, m), 0) else {}
)

-- for generating K as an S~-module
pocketIndicesS = method()
pocketIndicesS(ZZ,ZZ) := (d1, e1) -> (
  flatten for e from 1 to e1 list
    for d from (d1 + if e == e1 then 1 else 0) to max'd(e) list ((d, e), 0)
);

-*
pocketIndices = method();
pocketIndices(ZZ,ZZ) := (d1, e1) -> (
  pocketIndices1(d1,e1) | pocketIndicesS(d1,e1)
)
*-
pocketIndices = pocketIndices1

-- More helper methods
ranks = method()
ranks(HashTable) := tab -> new HashTable from for entry in pairs tab list (
  (key, vectors) := entry;
  rk := rank (coefficients matrix {vectors})_1;
  -* 
  if rk < #vectors then
  print("Dropped from " | toString(#vectors) | " to " | toString(rk) | " in weight " |
      toString(key)
    );
  *-
  (key, rk)
);

examinePocket = method()
examinePocket(Sequence,Sequence,ZZ) := (de0, de1, k) -> (
  print graph sum for entry in pairs ranks getPocket(de0,de1,k) list (
    (weight, rk) := entry;
    rk * xmon weight
  )
)

-- Given (d1, e1), find the pockets.
pockets = method(Options => {Verbose => true})
pockets(ZZ,ZZ) := opts -> (d1, e1) -> (
  combined := new HashTable;
  for dek in pocketIndices(d1, e1) do (
    (de0, k) := dek;
    combined = merge(combined,
      getPocket(de0, (d1, e1), k, Verbose => opts.Verbose), join
    )
  );
  combined
)

pockets(ZZ,ZZ,List) := opts -> (d1, e1, ww) -> (
  combined := {};
  for dek in pocketIndices(d1, e1) do (
    (de0, k) := dek;
    combined = combined | getPocket(
      de0, (d1, e1), k, ww, Verbose => opts.Verbose
    )
  );
  combined
)

-- Compute the *nonprimitive* K for given d and e.
nonprim = method(Options => {Verbose => true})
nonprim(ZZ,ZZ) := opts -> (d, e) -> (
  combined = pockets(d, e);
  rks = ranks combined;
  ans = sum for entry in pairs rks list (
    (weight, rk) := entry;
    rk * xmon weight
  );
  if opts.Verbose then (
    print graph ans;
    print toDigMats MSdecomp ans
  );
  ans
)

nonprimAll = method(Dispatch => Thing, Options => {emax => 30})
nonprimAll(Sequence) := opts -> () ->
  for e in 1..opts.emax do
    for d in e..max'd(e) do (
      print(d, e);
      nonprim(d, e, Verbose => true)
    )

-- Test the Frobenius generation hypothesis (Conjecture 4.1).
testFrob = method(Dispatch => Thing, Options => {emax => 30})
testFrob(Sequence) := opts -> () -> (
  errors = 0;
  for e in 1..opts.emax do
    for d in e..max'd(e) do (
      print(d, e);
      guess = nonprim(d, e, Verbose => false);
      actual = kappa(d,e);
      discrep = actual - guess;
      if makeHomogeneous discrep == 0 then
        print "Guess is correct"
      else (
        print "############## Discrepancy: ##############";
        print graph discrep;
        print toDigMats MSdecomp discrep;
        errors += 1
      )
    );
  errors
)

-- Helper method
quotientBasis = method()
quotientBasis(List,List) := (polysV, polysW) -> (
  R := commonRing(polysV | polysW);
  I := ideal(polysW) * R;
  ans := {};
  for apoly in polysV do (
    if apoly % I != 0 then (
      I = I + apoly;
      ans = ans | {apoly}
    )
  );
  ans 
)

primCache = new MutableHashTable;

-- Compute K(d,e)^prim.
Kprim = method(Options => {Verbose => true, OutputType => HashTable})
Kprim(ZZ,ZZ) := opts -> (d, e) -> (
  ans := null;
  if primCache#?(d, e) then (
    ans = primCache#(d, e)
  ) else (
    thepockets := pockets(d, e, Verbose => opts.Verbose);
    theh0 := K(d, e, Verbose => opts.Verbose);
    ans = new MutableHashTable;
    for entry in pairs theh0 do (
      (weight, kerElts) := entry;
      if thepockets#?weight then (
        q := quotientBasis(kerElts, thepockets#weight);
        if #q > 0 then (
          ans#weight = q
        )
      ) else (
        ans#weight = kerElts
      )
    );
    primCache#(d, e) = ans
  );
  if opts.OutputType === HashTable then
    ans
  else if opts.OutputType === List then
    for entry in pairs ans list (
      wt, coef := entry;
      wt => coef
    )
  else if opts.OutputType === RingElement then
    toCharacter(ans, Verbose => false)
  else if opts.OutputType === Expression then
    toExp MSdecomp toCharacter(ans, Silent => true)
  else if opts.OutputType === Matrix then
    toDigMats MSdecomp toCharacter(ans, Silent => true)
)

Kprim(ZZ,ZZ,List) := opts -> (d, e, ww) -> (
  thepockets := pockets(d, e, ww, Verbose => opts.Verbose);
  theh0 := H0b(d, e, ww);
  ans := {};
  quotientBasis(theh0, thepockets)
)

primChar = method(Options => {Verbose => true})
primChar(ZZ,ZZ) := opts -> (d, e) -> (
  toCharacter(Kprim(d, e, Verbose => opts.Verbose), Silent => true)
)

printPrim = method()
printPrim(ZZ,ZZ,List) := (d, e, ww) -> for alpha in Kprim(d, e, ww) do (
  print graph plift alpha
)

primAll = method(Dispatch => Thing, Options => {emax => 8})
primAll(Sequence) := opts -> () ->
  netList for e in 1..opts.emax list (
    reverse for d in reverse(0..e-1) list (
      print(d, e);
      ch := primChar(d, e, Verbose => false);
      MSdecomp ch;
      print graph ch;
      hamming ch
    )
  )

-- Another test for Conjecture 4.1.
dryTest = method(Dispatch => Thing, Options => {emax => 20})
dryTest(Sequence) := opts -> () ->
  for d in 1 .. 100 do (
    print("Dry element " | toString(d));
    assert(primChar(d, d, Verbose => true) == 0) -- test on the borderline
  )

nim = arg -> (
  if instance(arg, ZZ) then (
    m := arg;
    print("Computing nim " | toString(m));
    ans = primChar(m - 1, m, Verbose => false);
    toDigMats MSdecomp ans
  ) else if arg == () then (
    for m in 1 .. 100 do (
      print nim(m)
    )
  ) else error arg
)

showPrim = method()
showPrim(ZZ,ZZ) := (d,e) -> (
  ans := Kprim(d, e, Verbose => false, OutputType => Matrix);
  << changeBase(e, p) << "_" << p << ": " << ans << endl << endl;
)

-- Compute a table of Prim polynomials (like Table 1), or, if the optional
-- parameter dif is set, of characters K(d,e)^prim with e - d == dif. 
-- Indices are printed in base p.
primTable = method(Dispatch => Thing, Options => {dif => 1, mmax => 30})
primTable(Sequence) := opts -> () -> (
  for m in max(opts.dif,1) .. opts.mmax do (
    showPrim(m - opts.dif, m)
  )
)

-------------------------------------------
-- Computing Prim polynomials by guessing.

-- Determine whether the digit relation is satisfied.
digitsAtLeast = method(TypicalValue => Boolean)
digitsAtLeast(ZZ,ZZ) := (a, b) -> (
  if a < b then return false;
  dig'a = adicExpansion(p, a);
  dig'b = adicExpansion(p, b);
  all(0 .. #dig'b - 1, i -> dig'a#i >= dig'b#i)
)

-- Digit decreasing partitions of s with k parts.
DDP = method();
DDP(ZZ) := s -> DDP(n, s)
DDP(ZZ, ZZ) := (k, s) -> DDP(k, s, 0)
DDP(ZZ, ZZ, ZZ) := DDP(ZZ, ZZ, Nothing) := (k, s, bound) -> (
  if k < 0 then error k;
  if s < 0 then error s;
  if k == 0 then return if s == 0 and bound == 0 then {{}} else {};
  if k == 1 then return if digitsAtLeast(s, bound) then {{s}} else {};
  
  flatten for a1 from 0 to floor(s/k) list (
    if not digitsAtLeast(a1, bound) then continue;
    for l in DDP(k - 1, s - a1, a1) list (l | {a1})
  )
)

-- Unsure if this is a necessary condition.
-*
checkCarryRange = method()
checkCarryRange(List) := term -> (
  m = sum term // 2 + 1;
  all(
    1..floorLog(p, max(m, 1)) + 1, k -> (
      carryType := 2*floor(m/p^k) - sum(for a in term list floor(a/p^k));
      carryType >= 0 and carryType <= n - 2
    )
  )
)
*-

Partition == Partition := (X,Y) -> toList X == toList Y

-- Patterns for the last digit are known.
checkLastDigit = method()
checkLastDigit(List) := term -> (
  ld := for x in term list x % p;
  if ld#0 == p - 1 then return false;
  -- Avoid division by 0 in case p = 2.
  if p == 2 then return true;
  --
  s = sum ld;
  tmin := ceiling(s/(p-2)) - 2;
  tmax := floor(s/(p-2));
  for t from tmin to tmax do (
    if not ld#?t or not ld#?(t+1) then continue;
    if ld#(t+1) != ld#t then continue;
    lambda := new Partition from 
      for i from t+2 to #ld-1 when ld#i > 0 list ld#i;
    mu := new Partition from reverse for i from 0 to t-1 list (p - 2 - ld#i);
    if lambda == conjugate mu then return true
  );
  return false;
)

DDPnim = method();
DDPnim(ZZ) := m -> select(DDP(m), checkLastDigit)

-- Guess Prim(m) based on some conjectured information about the structure
-- (Conjectures 4.7 and 4.9)
nimGuess = method(
  Options => {Verbose => true, Truncate => false, Silent => false,
  OutputType => Matrix, dif => 1, CustomExponents => null}
);
nimGuess(ZZ) := opts -> m -> (
  verb = opts.Verbose and not opts.Silent;
  exps := if opts.CustomExponents == null then DDPnim(2*m - opts.dif - 1)
    else opts.CustomExponents;
  ans := 0_S;
  ansexp := expression 0;
  ansMat := expression 0;
  ansList := {};
  for ex in exps do (
    if opts.Truncate and ex#0 < 2*p then continue;
    if opts.Truncate and not all(ex, i -> i%p == 0) then continue;
    coef := null;
    if verb then (
      print(digitMatrix ex)
    );
    coef = #Kprim(m - opts.dif, m, ex, Verbose => verb) -
      coefficient(xmon ex, ans);
    assert(coef <= 1);
    if verb then << "Coefficient: " << coef << endl;
    if coef != 0 then (
      ans = ans + coef * MS(ex);
      ansexp = ansexp + coef * (expression MS) ex;
      ansMat = ansMat + coef * expression digitMatrix ex;
      ansList = ansList | {ex => coef}
    )
  );
  if verb then << endl << graph ans << endl;
  if opts.OutputType === Matrix then
    ansMat
  else if opts.OutputType === Expression then
    ansexp
  else if opts.OutputType === RingElement then
    ans
  else if opts.OutputType === List then
    ansList
  else if opts.OutputType === HashTable then
    hashTable ansList
  else
    error opts.OutputType
)

summarizeTerms = () -> (
  nonzeros = apply(select(pairs nimCache, pair -> pair#1 != 0),
    pair -> (entries pair#0, pair#1)
  );
  for pair in sort nonzeros do (
    << pair#1 << matrix pair#0 << endl << endl;
  )
)

-- Guess nim table
primGuessAll = method(
  Dispatch => Thing, Options => {Truncate => false, dif => 1, mmax => 30}
)
primGuessAll(Sequence) := opts -> () -> (
  for m from max(opts.dif,1) to opts.mmax do (
    print ("Guessing Kprim(" | toString(m - opts.dif) | "," |
      toString(m) | ")"
    );
    print nimGuess(
      m, Verbose => false, Truncate => opts.Truncate,
      dif => opts.dif, OutputType => Matrix
    )
  )
)

primGuessTable = method(
  Dispatch => Thing, Options => {Truncate => false, dif => 1, 
  OutputType => Matrix, mmax => 30}
)
primGuessTable(Sequence) := opts -> () -> (
  for m from max(opts.dif,1) to opts.mmax do (
    << changeBase(m, p) << "_" << p << ": " << nimGuess(
      m, Verbose => false, Silent => true, Truncate => opts.Truncate,
      dif => opts.dif, OutputType => opts.OutputType
    ) << endl << endl
  )
)

-- Test the guesses against the actual values.
primTest = method(Dispatch => Thing, Options => {dif => 1});
primTest(ZZ) := opts -> m -> (
  << "Guessing nim " << changeBase(m, p) << "_" << p << endl;
  guess := nimGuess(m, dif => opts.dif, 
    Verbose => false, OutputType => RingElement
  );
  print toDigMats MSdecomp guess;
  << "Computing nim " << changeBase(m, p) << "_" << p << endl;
  actual := primChar(m - opts.dif, m, Verbose => false);
  discrep = value guess - value actual;
  if makeHomogeneous discrep == 0 then (
    print "Guess is correct";
    0
  ) else (
    print "############## Discrepancy: ##############";
    print graph discrep;
    print toDigMats MSdecomp discrep;
    1
  )
)

primTestAll = method(Dispatch => Thing, Options => {dif => 1, mmax => 30})
primTestAll(Sequence) := opts -> () -> (
  errors = 0;
  for m from max(1, opts.dif) to opts.mmax do (
    errors += primTest(m, dif => opts.dif);
  );
  errors
)
