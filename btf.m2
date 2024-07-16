-- This implements the algorithm described in
--
--   A. Pothen and C.-J. Fan: Computing the Block Triangular Form of a Sparse Matrix
--
-- for permuting the rows and columns of a given matrix to make it
-- more block-triangular. It is not clear if the result is optimal
-- but it should at least be passable.

needsPackage "Graphs";

-- Compute the block-triangular form of A using row and column permutations.
btf = A -> (
  transposed := false;
  if numrows(A) < numcols(A) then (
    A = transpose A;
    transposed = true;
  );
  C := toList(0 .. numcols(A)-1);
  R := toList(0 .. numrows(A)-1);
  -- Step 1: Coarse decomposition.
  M := maximumMatching(A,R,C);
  (VR, HR, SR, VC, HC, SC) := coarseDecomposition(A,R,C,M);
  -- Step 2: Fine decompositions.
  (VR, VC) = diagonalDecomposition(A,VR,VC);
  (HR, HC) = diagonalDecomposition(A,HR,HC);
  (SR, SC) = fineDecomposition(A,SR,SC,M);
  -- Return the permuted matrix.
  A = submatrix(A, VR|SR|HR, VC|SC|HC);
  if transposed then transpose A
  else A
);

-- Delete all of L1 from L2 while keeping order (which is not guaranteed
-- if we did instead toList(set(L2) - set(L1))).
deleteAll = (L1,L2) -> fold((L,x) -> delete(x,L), L2, L1);

-- Find a maximum matching in the bipartite graph.
maximumMatching = (A,R,C) -> (
  M := {};
  U := {};
  -- Step 1: Cheap matching.
  mrows := {};
  for c in C do (
    matched := false;
    for r in R do (
      if A_(r,c) != 0 and not member(r, mrows) then (
        M = append(M, (r,c));
        mrows = append(mrows, r);
        matched = true;
        break;
      );
    );
    if not matched then U = append(U, c);
  );
  -- Step 2: Augment matching.
  while true do (
    Unew := {};
    mrows = {};
    for c in U do (
      p := augmentingPath(A, R, C, M, c, mrows);
      if p == null then Unew = append(Unew, c)
      else (
        -- Mark visited rows
        mrows = mrows | apply(select(0..#p-1, odd), i -> p#i);
        M = augmentMatching(M, p);
      );
    );
    if U == Unew then break
    else U = Unew;
  );
  M
);

-- Search for an augmenting path from c. Never consider rows in the
-- marked set mrows.
augmentingPath = (A, R, C, M, c, mrows) -> (
  -- This proceeds recursively in a depth-first manner:
  -- We go from c to a row r (outside of M). If r is unmatched, we found
  -- an augmenting path. If r is matched to column d, we follow that edge
  -- and recurse with d, marking r as used for that branch.
  for r in R do (
    if A_(r,c) == 0 or member(r, mrows) then continue;
    E := select(M, e -> e#0 == r);
    if #E == 0 then return {c,r}
    else (
      for e in E do (
        d := e#1;
        q := augmentingPath(A, R, C, M, d, mrows|{r});
        if q != null then return {c,r} | q;
      );
    );
  );
  null
);

-- This is similar to augmentingPath but instead of finding just an
-- augmenting path, it returns all rows and columns reachable from
-- the start vertex by an alternating path.
alternatingRC = (A,R,C,M,c,mrows) -> (
  -- Implementation is similar to augmentingPath.
  AR := {};
  AC := {c};
  for r in R do (
    if A_(r,c) == 0 or member(r, mrows) then continue;
    E := select(M, e -> e#0 == r);
    if #E == 0 then (
      AR = append(AR, r);
    )
    else (
      for e in E do (
        d := e#1;
        (ar, ac) := alternatingRC(A, R, C, M, d, mrows|{r});
        AR = AR|{r}|ar;
        AC = AC|ac;
      );
    );
  );
  (sort(toList(set(AR))), sort(toList(set(AC))))
);

-- Convert a path (list of adjacent vertices) that starts with a column
-- into a list of (r,c) edges where the row always comes first.
pathEdges = p -> (
  a := p#0;
  apply(1 .. #p-1, i -> (
    b := p#i;
    x := if odd(i) then (b,a) else (a,b);
    a = b;
    x
  ))
);

-- Augment M with p, i.e., compute the symmetric difference of their
-- edge sets.
augmentMatching = (M, p) -> (
  E := pathEdges p;
  sort toList((set(M) - set(E)) + (set(E) - set(M)))
);

-- Compute the coarse decomposition.
coarseDecomposition = (A,R,C,M) -> (
  -- Identify horizontal block.
  HU := select(C, c -> all(R, r -> not member((r,c), M)));
  HR := {};
  HC := {};
  for c in HU do (
    (hr, hc) := alternatingRC(A,R,C,M,c,{});
    HR = HR|hr;
    HC = HC|hc;
  );
  HR = sort(toList(set(HR)));
  HC = sort(toList(set(HC)));
  -- Identify vertical block.
  VU := select(R, r -> all(C, c -> not member((r,c), M)));
  VR := {};
  VC := {};
  for r in VU do (
    -- alternatingRC is written from the perspective of an unmatched column.
    -- To apply it to unmatched rows, we transpose all the data and results.
    (vc, vr) := alternatingRC(transpose(A),C,R,M/reverse,r,{});
    VR = VR|vr;
    VC = VC|vc;
  );
  VR = sort(toList(set(VR)));
  VC = sort(toList(set(VC)));
  -- Finish.
  SR := deleteAll(VR|HR, R);
  SC := deleteAll(VC|HC, C);
  (VR, HR, SR, VC, HC, SC)
);

-- Reorder R and C so that the elements of each connected component
-- in the bipartite graph are adjacent.
diagonalDecomposition = (A,R,C) -> (
  V := apply(R, r -> "r"|toString(r)) | apply(C, c -> "c"|toString(c));
  lut := new HashTable from (
    apply(R, r -> "r"|toString(r) => r) |
    apply(C, c -> "c"|toString(c) => c)
  );
  E := delete(null, apply(R**C, (r,c) -> if A_(r,c) != 0 then {"r"|toString(r), "c"|toString(c)}));
  G := graph(V, E);
  comps := connectedComponents G;
  R = flatten apply(comps, D -> delete(null, apply(D, d -> if d_0 == "r" then lut#d)));
  C = flatten apply(comps, D -> delete(null, apply(D, d -> if d_0 == "c" then lut#d)));
  (R, C)
);

-- There are better, linear-time algorithms for this but for now we
-- have this one which is quick to implement.
stronglyConnectedComponents = G -> (
  V := vertices G;
  D := new HashTable from apply(V, v -> v => descendents(G, v));
  E := select(V**V, (v,w) -> member(v, D#w) and member(w, D#v));
  connectedComponents graph(V, E)
);

-- Compute the fine decomposition of the square submatrix of A with
-- rows R and columns C on which M is a perfect matching. Returns a
-- reordering of R and C so that elements of the same block are
-- adjacent and non-zeros are only in the upper triangle.
fineDecomposition = (A,R,C,M) -> (
  -- Compute the graph G_d by oriented non-matching edges from columns to
  -- rows and contracting matching edges, then identifying all vertices
  -- with the rows.
  m := new HashTable from apply(M, (r,c) -> r => c);
  V := R;
  E := select(V**V, (r1,r2) -> A_(r2,m#r1) != 0 and not member((r2,m#r1), M));
  Gd := digraph(V,E);
  Rs := stronglyConnectedComponents Gd;
  -- Use the matching to recover the corresponding column sets Cs from Rs
  Cs := apply(Rs, R -> apply(R, r -> m#r));
  -- To make the matrix block-triangular, we compute the topological
  -- sorting of a directed graph based on Lemma 2.6 in the paper.
  V = toList(0..#Cs-1);
  E = select(V**V, (j,i) -> i != j and not all((Rs#i)**(Cs#j), (r,c) -> A_(r,c) == 0));
  G := digraph(V, E);
  T := topologicalSort(G, "degree");
  Rs = apply(T, i -> Rs#(T#i));
  Cs = apply(T, i -> Cs#(T#i));
  (flatten(Rs / sort), flatten(Cs / sort))
);
