-- For pasting:
-- load("general.m2")

-- For testing general hypotheses on the structure of kappa(d,e) (Conj. 4.10).

needs "prim.m2"

-- Guess based on double truncation. Seems to give correct answers for n = 3
-- and for p = 2, but not in general.
guess'kappa = method()
guess'kappa(ZZ,ZZ) := (d,e) -> (
  sum for r from 1 to floorLog(p, e) list (
    prmmin := d - (p^r - 1)*(n - 1) + p^r;
    prmmax := e;
    sum for m from max(1,ceiling(prmmin/p^r)) to floor(prmmax/p^r) list (
      ddd := p^r * m - prmmin;
      eee := prmmax - p^r * m;
      print("Found Nim term: r = " | r | ", m = " | m | ", with " |
        toString (ddd // p^r, eee // p^r) | " truncations"
      );
      ans := (Frobk r) (primChar(m-1,m, Verbose => false)) *
      (sum for i from 0 to ddd // p^r list
        (sum for j from 0 to eee // p^r list
          (-1)^(i + j) * (Frobk r) Schur(n - i : 1) * (Frobk r) Schur(j : 1) *
          Schur((1 : eee + ddd - j*p^r) | (n - 2 : ddd) | (1 : i*p^r))
        )
      ) // x_all^(ddd + 1);
      ans
    )
  )
)

test = method()
test(ZZ,ZZ) := (d,e) -> (
  print (d,e);
  guess := guess'kappa(d,e);
  actual := contents K(d,e);
  discrep := makeHomogeneous(actual - guess);
  if discrep != 0 then (
    print("Missing term at " | toString(d,e) | ":");
    print toDigMats MSdecomp discrep
  ) else (
    print("Guess is correct")
  )
)
test(ZZ) := e ->
  for d in e..max'd(e) do
    test(d,e)
testAll = method(Dispatch => Thing, Options => {emax => 30})
testAll(Sequence) := opts -> () -> (
  print("n = " | n | ", p = " | p);
  for e in 1..opts.emax do
    test(e)
)
-- Test the edge case, which tends to give the most trouble.
testEdge = method(Dispatch => Thing, Options => {emax => 30})
testEdge(Sequence) := opts -> () -> (
  for e in 1..opts.emax do
    test(e,e)
)

-- Display the inner structure of the aforesaid guess.
inspectGuess = method()
inspectGuess(ZZ,ZZ) := (d,e) -> (
  if d < e then error(d,e);
  sum for r from 1 to floorLog(p, e) list (
    prmmin := d - (p^r - 1)*(n - 1) + p^r;
    prmmax := e;
    ansall = sum for m from max(1,ceiling(prmmin/p^r)) to floor(prmmax/p^r) list (
      ddd := p^r * m - prmmin;
      eee := prmmax - p^r * m;
      print("Found Nim term: r = " | r | ", m = " | m | ", with " |
        toString (ddd // p^r, eee // p^r) | " truncations"
      );
      print("d' = " | ddd);
      print("e' = " | eee);
      ans := (Frobk r) (primChar(m-1,m, Verbose => false)) *
      (sum for i from 0 to ddd // p^r list
        (sum for j from 0 to eee // p^r list (
          << "Multiplying Nim " << m
          << " * F^" << r << "(Schur" << (n-i : 1) << " * "
          << " Schur" << (j : 1) << ") * "
          << (-1)^(i + j) * expression(symbol Schur)
          << ((1 : eee + ddd - j*p^r) | (n - 2 : ddd) | (1 : i*p^r))
          << " to get " << endl <<
          toDigMats MSdecomp (
            (Frobk r) (primChar(m-1,m, Verbose => false)) *
            (-1)^(i + j) * (Frobk r) Schur(n - i : 1) * (Frobk r) Schur(j : 1) *
            Schur((1 : eee + ddd - j*p^r) | (n - 2 : ddd) | (1 : i*p^r)) // x_all^(ddd + 1)
          ) << endl;
          (-1)^(i + j) * (Frobk r) Schur(n - i : 1) * (Frobk r) Schur(j : 1) *
            Schur((1 : eee + ddd - j*p^r) | (n - 2 : ddd) | (1 : i*p^r))
        ))
      ) // x_all^(ddd + 1);
      print "Total for this term:";
      print toDigMats MSdecomp ans;
      ans
    );
    print "Total overall:";
    print toDigMats MSdecomp ansall;
    ansall
  )
)