needs "prim.m2"

-- A notion of tile that breaks down when p = 3, n = 5, m = 24.
-*
TileRing = ZZ[P,D];
TileRing ? TileRing := (X,Y) -> (
  ans1 := coefficient(P, X) ? coefficient(P, Y);
  if ans1 != (symbol ==) then return ans1;
  ans2 := coefficient(D, X) ? coefficient(D, Y);
  if ans2 != (symbol ==) then return ans2;
  return coefficient(1_TileRing, X) ? coefficient(1_TileRing, Y);
)
*-

-- A tile has five parts:
--   - In and out carries (explained in text)
--   - lambda: constants that end v
--   - mu: constants to be subtracted from p-1 (p-2 for end tiles) to begin v
--   - nu: constant to be subtracted from the digit k to get the repeated digit in the middle of v (unclear if this is a good notion).
-- The coefficient epsilon is not stored in the tile, but the given methods (mineTiles, etc.) return hash tables (tile => epsilon).
Tile = new Type of BasicList
Tile.synonym = "tile"

knownTiles = new MutableHashTable;

tile = method(Dispatch => Thing);
tile(Sequence) := args -> (
  (tOut, tIn, lambda, mu, nu) := args;
  new Tile from (
    tOut_ZZ, tIn,
    new Partition from lambda,
    new Partition from mu,
    nu
  )
)
expression Tile := t -> (
  (tOut, tIn, lambda, mu, nu) := toSequence t;
  (symbol Tile) expression(tOut, tIn,
    (for a in mu list (symbol p - expression(
      a + if tIn === "END" then 2 else 1))
    ) |
    {symbol k + expression nu, symbol k + expression nu} | toList lambda
  )
)
net Tile := z -> net expression z;
toString Tile := z -> toString expression z;
tex Tile := z -> tex expression z;
html Tile := z -> html expression z;

removeTrailingZeros = method(Dispatch => Thing);
removeTrailingZeros(BasicList) := l -> (
  take(l, (pos := position(l, elt -> (elt != 0), Reverse => true);
    if pos === null then 0 else 1 + pos)
  )
)

extractTiles = method();
extractTiles(Matrix) := M -> (
  lists := reverse entries transpose M;
  -- Get sum d.
  m := sum(for i from 0 to (numColumns M - 1) list sum(lists_i) * p^i)/2;
  try (
    m = lift(m,ZZ)
  ) else error("Invalid tile" | net M | ": odd total");
  digits := adicExpansion(p, m+1);
  carries := for i from 0 to (numColumns M - 1) list lift(
    (sum(for j from 0 to i list (sum(lists_j) * p^j)) - 2*((m+1) % p^(i+1) - 1))/p^(i+1), ZZ
  );
  -- print ("carries: " | toString carries);
  for i from 0 to (numColumns M - 1) list (
    tOut = carries#i;
    tIn = if i > 0 then carries#(i-1) else "END";
    col = lists#i;
    if col#tOut != col#(tOut + 1) then
      error("Invalid tile with column" | toString col | ", carry " | tOut );
    nu = col#tOut - digits#i;
    lambda = removeTrailingZeros take(col, -(#col - tOut - 2));
    mu = removeTrailingZeros reverse apply(take(col, tOut), x -> p -
      (if tIn === "END" then 2 else 1) - x
    );
    tile(tOut, tIn, lambda, mu, nu)
  )
)

harvestTiles = method()
harvestTiles(List) := nimList -> (
  for entry in nimList do (
    -- print entry;
    (ex, coef) := toSequence entry;
    mat := digitMatrix ex;
    tiles := extractTiles mat;
    newTiles := {};
    knownCoef := 1;
    for tile in tiles do (
      if knownTiles#?tile then (
        knownCoef = knownCoef * knownTiles#tile;
      ) else (
        -- print tile;
        newTiles = newTiles | {tile}
      )
    );
    if #newTiles == 0 then (
      if coef != knownCoef then (
        error ("Expected coef " | knownCoef | ", got " | coef)
      )
    ) else if #newTiles == 1 then (
      << endl;
      print(newTiles#0 => lift(coef/knownCoef, ZZ));
      knownTiles#(newTiles#0) = lift(coef/knownCoef, ZZ)
    ) else if coef == knownCoef then (
      << endl;
      for tile in newTiles do (
        print(tile => 1);
        knownTiles#tile = 1
      )
    ) else (
      error (toString coef | "to be split among " | #newTiles |
        " tiles")
    )
  )
)

-- Find tiles (as in Tables 2-4) by "mining" the Prim polynomials for a range
-- of values for n, p, and m. 
-- Option maxtime: After a computation takes this many seconds, move on to the
-- next value of n or p.
mineTiles = method(
  Dispatch => Thing, Options => {nmin => 4, nmax => 6, pmin => 3, pmax => 11,
    mmin => 1, mmax => 100, maxtime => 5
  }
);
mineTiles(Sequence) := opts -> () -> (
  for nn from opts.nmin to opts.nmax do (
    for pp from opts.pmin to opts.pmax do (
      if not isPrime pp then continue;
      n = nn;
      p = pp;
      << endl << "------" << endl << "m = " << flush;
      updatenp();
      for m from opts.mmin to opts.mmax do (
        << m << "." << flush;
        tv := timing nimGuess(m, Silent => true, OutputType => List);
        (t, nimList) := toSequence tv;
        harvestTiles nimList;
        if t > opts.maxtime then (
          << "time: " << t << endl;
          break
        )
      )
    )
  );
  peek knownTiles
)