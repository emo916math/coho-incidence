n = 3; -- changeable
p = 3; -- changeable
truncateOutput 150 -- because the current methods tend to flood the screen

needs "print.m2" -- for triGraph, etc.
needsPackage "TestIdeals"; -- for floorLog and adicExpansion

-- Update definitions to reflect new values of n and p, which we often need to
-- change in the middle of a session.
updatenp = () -> (
  
  -- Warning: the notations of the program and the paper do not always align:
  -- S (roughly) corresponds to A of paper
  -- Sp = S of paper
  
  S = ZZ[x_1..x_n];
  x_all = product(toList(x_1..x_n));
  hamming = map(ZZ, S, toList(n:1));
  Sp = (GF p)[z_1..z_n];
  omega = sum(toList(z_1..z_n));
  
  xmon = method();
  xmon(Sequence) := xmon(List) := w -> product(n, i -> x_(i+1)^(w_i));
    
  zmon = method();
  zmon(Sequence) := zmon(List) := w -> product(n, i -> z_(i+1)^(w_i));
  
  dispk = method();
  dispk(RingElement, ZZ) := (pol, k) -> (
    polh = makeHomogeneous(pol);
    if k == 1 then return leadCoefficient polh;
    if polh == 0 then return {};
    coefs := flatten entries(coefficients(polh, Variables => x_k, Monomials =>
      for i in (0..degree(x_k, polh)) list x_k^i
    ))_1;
    return for po in coefs list dispk(po, k - 1)
  );
  dispk(RingElement) := pol -> dispk(pol, n);
  dispk(ZZ, ZZ) := (a, k) -> dispk((map(S, ZZ)) a, k);
  dispk(ZZ) := a -> dispk(a, n);
  
  graph0 = method();
  graph0(Thing, ZZ) := (l, k) -> (
    if k <= 0 then error k;
    if k == 1 then return triGraph({{l}});
    if k == 2 then return triGraph({l});
    if k == 3 then return triGraph(l);
    subgraphs = for item in l list graph0(item, k - 1);
    if k % 2 == 1 then
      return stack mingle(subgraphs, #subgraphs - 1 : stack(k//2-1 : " "))
    else
      return horizontalJoin mingle(subgraphs,
        #subgraphs - 1 : concatenate(k//2-1)
      )
  );
  graph0(Thing) := l -> graph0(l, n);
  
  graph = method();
  graph(S) := graph(ZZ) := a -> graph0 dispk a;
  graph(Sp) := a -> graph plift a;
  
  ---------------------------------------------------------
  
  SchurNum = method(Dispatch => Thing);
  SchurNum(List)     :=
  SchurNum(Sequence) := exps -> (
    det(matrix(
      for i in 1..n list
        for j in 0..n-1 list
          x_i^(n-1-j + if exps#?j then exps#j else 0)
      )
    )
  );
  SchurNum(ZZ) := n -> SchurNum (1:n);
  SchurDenom = SchurNum(); -- Schur denominator, a.k.a. Vandermonde
  
  Schur = method(Dispatch => Thing);
  Schur(Thing) := exps -> (
    -- print concatenate("Computing Schur", toString(exps));
    SchurNum exps // SchurDenom
  );
  
  schurDecomp = method();
  schurDecomp(S) := f -> (
    ans := {};
    while f != 0 do (
      lc := leadCoefficient f;
      exps := toSequence first exponents leadMonomial f;
      ans = ans | {exps => lc};
      f = f - lc * Schur(exps)
    );
    ans
  );
  schurDecomp(ZZ) := k -> {splice {n:0} => k};
  
  ---------------------------------------------------------
  
  TruncSym = method();
  TruncSym(ZZ, ZZ) := (k, n) -> sum(
    for term in (entries monomials Schur k)_0
    list if all((exponents term)_0, z -> z < p^n) then term else 0
  );
  
  wedge = method();
  wedge(ZZ,RingElement) := (k, f) -> wedge(k, terms(f));
  wedge(ZZ,List) := (k, l) -> (
    if k == 0 then
      1
    else if k == 1 then
      sum(l)
    else if #l == 0 then
      0
    else if #l == 1 then (
      (mon, coef) := coefficients l_0;
      mon0 := mon_(0,0); coef0 := lift(coef_(0,0), ZZ);
      binomial(coef0, k) * mon0^k
    ) else (
      split := #l//2;
      leftHalf := l_{0..split - 1};
      rightHalf := l_{split..#l - 1};
      sum(for i in 0..k list wedge(i, leftHalf) * wedge(k - i, rightHalf))
    )
  );
  
  sym = method();
  sym(ZZ,RingElement) := (k, f) -> sym(k, terms(f));
  sym(ZZ,List) := (k, l) -> (
    if k == 0 then
      1
    else if k == 1 then
      sum(l)
    else if #l == 0 then
      0
    else if #l == 1 then (
      (mon, coef) := coefficients l_0;
      mon0 := mon_(0,0); coef0 := lift(coef_(0,0), ZZ);
      binomial(coef0 + k - 1, k) * mon0^k
    ) else (
      split := #l//2;
      leftHalf := l_{0..split - 1};
      rightHalf := l_{split..#l - 1};
      sum(for i in 0..k list sym(i, leftHalf) * sym(k - i, rightHalf))
    )
  );
  
  ---------------------------------------------------------
  
  dualize = map(S, S, for i from 1 to n list x_all // x_i);
  
  Frob = map(S, S, for i from 1 to n list x_i^p);
  
  Frobk = method();
  Frobk(ZZ) := k -> (
    if k == 0 then map(S,S);
    map(S, S, for i from 1 to n list x_i^(p^k))
  );
  
  Frobp = map(Sp, Sp, for i from 1 to n list z_i^p);
  
  Frobpk = method();
  Frobpkcache = new MutableHashTable;
  Frobpk(ZZ) := k -> (
    if Frobpkcache#?k then Frobpkcache#k else (
      ans = if k == 0 then map(Sp,Sp) else (
        map(Sp, Sp, for i from 1 to n list z_i^(p^k))
      );
      Frobpkcache#k = ans;
      ans
    )
  );
  
  makeHomogeneous = method();
  makeHomogeneous(RingElement) := pol -> (
    deg := first degree pol;
    ret = sum(
      for t in terms(pol) list t*x_all^(
        try lift((deg - first degree t)/n, ZZ)
          else error(deg, ",", first degree t)
      )
    );
    promote(ret, ring pol) -- don't return the integer 0
  );
  
  -- Lifting from Sp to S; least nonnegative remainder.
  modp = map(Sp, S, for i in 1..n list z_i);
  plift0 = map(S, Sp, for i in 1..n list x_i);
  plift = method();
  plift(Sp) := S => f -> (
    f0 := plift0(f);
    if zero(f0) then return f0;
    coefs0 := coefficients f0;
    coefs := (coefs0_0, vector(for num in entries(coefs0_1) list
      (lift(first num, ZZ) % p)
    ));
    first entries times(coefs)
  );
  plift(List) := l -> for i in l list plift i;
  plift(Matrix) := m -> matrix plift entries m;
  plift(Vector) := v -> vector plift entries v;
  
  tuples = method();
  tuples(ZZ,BasicList) := (k,l) -> (
    if k < 0 then error k;
    if k == 0 then return {{}};
    flatten for a in l list for t in tuples(k-1, l) list {a} | t
  );
  
  -- A recursive method to compute all k-tuples of nonnegative integers
  -- with sum s.
  tuplesWithSum = method();
  tuplesWithSum(ZZ,ZZ) := (k,s) -> (
    if k < 0 then error k;
    if s < 0 then return {};
    if k == 0 and s == 0 then return {{}};
    if k == 0 then return {};
    tuplesWithSumHelper(k,s)
  );
  tuplesWithSumHelper = method();
  tuplesWithSumHelper(ZZ,ZZ) := (k,s) -> (
    if k == 1 then return {{s}};
    flatten(for i from 0 to s list for l in tuplesWithSumHelper(k-1,s-i) list
      {i} | l
    )
  );
  
  -- To discover formulas for Nim polynomials.
  -- Minimal Schur function with a given exponent.
  MS = method(Dispatch => Thing);
  MS(BasicList) := exps -> (
    if #exps != n then error exps;
    diffs := for i from 0 to n-1 list (
      exps_i - if i == n-1 then 0 else exps_(i+1)
    );
    digits := for d in diffs list adicExpansion(p,d);
    promote(product for k from 0 to max(for ex in digits list #ex) - 1 list (
      (Frobk k) Schur(
        tot := 0;
        reverse for i in reverse(0..n-1) list (
          tot = tot + if digits_i#?k then digits_i_k else 0
        )
      )
    ), S)
  );
  
  MSdecomp = method();
  MSdecomp(S) := f -> (
    ans := {};
    while f != 0 do (
      lc := leadCoefficient f;
      exps := toSequence first exponents leadMonomial f;
      ans = ans | {exps => lc};
      f = f - lc * MS(exps)
    );
    ans
  );
  MSdecomp(ZZ) := k -> MSdecomp promote(k,S);
  
  toExp = method();
  toExp(List) := decomp -> sum for opt in decomp list (
    (exps, coef) := toSequence opt;
    coef * (expression MS) exps
  );
  
  zeroPad = method();
  zeroPad(List,ZZ) := (l, len) -> (
    l | toList(len - #l : 0)
  );
  
  digitMatrix = method(Dispatch => Thing);
  digitMatrix(BasicList) := term -> (
    digits := for d in term list adicExpansion(p, d);
    max'digits := max({1} | for d in digits list #d);
    digits'pad := for d in term list
      reverse zeroPad(adicExpansion(p, d), max'digits);
    matrix digits'pad
  );
  
  difMat = 1 - ((matrix {n-1 : {0}} | 1) || matrix {{n : 0}});
  differenceDigitMatrix = method(Dispatch => Thing);
  differenceDigitMatrix(BasicList) := term -> (
    -- if all(term, entry -> entry == 0) then 1 else
    difMat^-1 * digitMatrix entries difMat vector toList term
  );
  
  toDigMats = method();
  toDigMats(List) := decomp -> expression 0 + sum for opt in decomp list (
    (exps, coef) := toSequence opt;
    coef * expression differenceDigitMatrix exps
  );
  
  
  -- For printing K collections
  toCharacter = method(Options => {Verbose => true, Silent => false});
  toCharacter(HashTable) := opts -> t -> (
    tot = 0_S;
    for entry in pairs t do (
      (weight, kerElts) = entry;
      if opts.Verbose and not opts.Silent then (
        print weight;
        for kerElt in kerElts do (
          print graph plift kerElt;
          print ""
        )
      );
      tot = tot + #kerElts * xmon weight
    );
    
    if not opts.Silent then (
      print "Total character:";
      print graph tot;
      print toDigMats MSdecomp tot;
    );
    tot
  );
  
  contents = method();
  contents(HashTable) := t -> toCharacter(t, Silent => true);
  
  << "n = " << n << endl;
  << "p = " << p << endl;
  
  -- For prim.m2: clear cache
  primCache = new MutableHashTable;
  
  -- For pockets.m2: update pockets
  if instance(renewPockets, Function) then renewPockets();
);

updatenp()