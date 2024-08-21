-- Flag for whether to use shading instead of numbers to denote coefficients
-- from 1 to 4 in symmetric polynomials.
useShading = false;

-- For debugging.
printAndReturn = x -> (print x; print ""; x)

myLoaded = () -> select(values loadedFiles, str -> match("evan", str))

-- Remove whitespace from the edges of a net.
trimNet = method();
trimNet(Net) := n -> (
  s := unstack n;
  
  -- Trim top.
  while s#?0 and (for ch in s#0 do (
      if ch != " " then break 1
    )) === null do (
      s = drop(s, 1);
  );
  -- Trim bottom.
  while s#?0 and (for ch in s#-1 do (
      if ch != " " then break 1
    )) === null do (
      s = drop(s, -1);
  );
  -- Trim left.
  while (for line in s do (
    if #line > 0 then break 1
  )) =!= null and (for line in s do (
    if #line > 0 and line#0 != " " then break 1
  )) === null do (
    s = apply(s, line -> concatenate(drop(toSequence line, 1)))
  );
  -- Trim right.
  s = apply(s, line -> (
    l = toSequence line;
    while l#?0 and l#-1 == " " do
      l = drop(l, -1);
    concatenate l
  ));
  
  stack s
)

triGraph = l -> (
  curNet = stack();
  for n in 0..length(l)-1 do (
    line = l_n;
    curLine = concatenate(n : " ");
    for entry in line do (
      if entry == 0 then
        curLine = curLine | "  "
      else if useShading and entry == 1 then
        curLine = curLine | "░░"
      else if useShading and entry == 2 then
        curLine = curLine | "▒▒"
      else if useShading and entry == 3 then
        curLine = curLine | "▓▓"
      else if useShading and entry == 4 then
        curLine = curLine | "██"
      else if #toString(entry) == 1 then
        curLine = curLine | " " | entry -- nbsp to avoid collisions
      else if #toString(entry) == 2 then
        curLine = curLine | entry
      else
        curLine = curLine | "██"
    );
    curNet = curLine || curNet -- print from bottom to top
  );
  trimNet curNet
)