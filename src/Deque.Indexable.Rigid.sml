functor ImplicitRigidDeque (val base : int) :> INDEXABLE_DEQUE =
struct
  open Unrank
  
  datatype 'a tree = Leaf of 'a | Node of 'a tree list | Rev of 'a tree list
  
  fun revT (Leaf x) = Leaf x
    | revT (Node x) = Rev x
    | revT (Rev x) = Node x
  
  fun loop (xs, nil) = xs
    | loop (xs, y :: ys) = loop (revT y :: xs, ys)
  
  fun revL xs = loop (nil, xs)
  
  (*  Invariants:  Consider m = Many (x, r, y).
   *  
   *  - x and y must not be simultaneously empty.
   *  - x and y must be both non-empty if m is in the top level.
   *  - x and y individually must have less than 2k elements.
   *)
  
  datatype 'a deque
    = Empty
    | Pure of 'a tree
    | Cons of 'a tree * 'a deque ref
    | Snoc of 'a deque ref * 'a tree
    | Many of 'a tree list * 'a deque ref * 'a tree list
  
  fun pair (x, y) = Many (x, ref Empty, y)
  fun many (x, xs, ys, zs, z) = Many (x, ref (Many (xs, ys, zs)), z)
  
  fun few (x :: nil) = Pure x
    | few xs = let val (x, y) = split xs in pair (x, revL y) end
  
  fun wef (x :: nil) = Pure (revT x)
    | wef xs = let val (x, y) = split xs in pair (revL y, x) end
  
  fun consF (xs, ys, zs) =
    case halve (base, xs) of
        NONE => Many (xs, ys, zs)
      | SOME (ws, xs) => Many (ws, ref (Cons (Node xs, ys)), zs)
  
  fun snocF (xs, ys, zs) =
    case halve (base, zs) of
        NONE => Many (xs, ys, zs)
      | SOME (ws, zs) => Many (xs, ref (Snoc (ys, Node zs)), ws)
  
  fun consT (x, Many (xs, ys, zs)) = consF (x :: xs, ys, zs)
    | consT (x, Pure y) = pair (x :: nil, revT y :: nil)
    | consT (x, _) = Pure x
  
  fun snocT (Many (xs, ys, zs), z) = snocF (xs, ys, z :: zs)
    | snocT (Pure x, y) = pair (x :: nil, y :: nil)
    | snocT (_, x) = Pure (revT x)
  
  (*  Inductively, zs is nonempty.  *)
  fun unconsT (Many (Node x :: xs, ys, zs), z) = many (x, xs, ys, zs, z)
    | unconsT (Many (Rev x :: xs, ys, zs), z) = many (revL x, xs, ys, zs, z)
    | unconsT (Pure (Node x), y) = pair (x, y)
    | unconsT (Pure (Rev x), y) = pair (revL x, y)
    | unconsT (_, x) = wef x
  
  (*  Inductively, xs is nonempty.  *)
  fun unsnocT (x, Many (xs, ys, Node z :: zs)) = many (x, xs, ys, zs, z)
    | unsnocT (x, Many (xs, ys, Rev z :: zs)) = many (x, xs, ys, zs, revL z)
    | unsnocT (x, Pure (Node y)) = pair (x, revL y)
    | unsnocT (x, Pure (Rev y)) = pair (x, y)
    | unsnocT (x, _) = few x
  
  datatype 'a step
    = C of 'a tree
    | S of 'a tree
    | Uc of 'a tree list
    | Us of 'a tree list
    | M of 'a deque ref
  
  (*  Inductively, x and y are not simultaneously empty in Many (x, r, y).  *)
  fun build (Cons (x, r), ss) = build (!r, M r :: C x :: ss)
    | build (Snoc (r, x), ss) = build (!r, M r :: S x :: ss)
    | build (Many (nil, r, x), ss) = build (!r, M r :: Uc x :: ss)
    | build (Many (x, r, nil), ss) = build (!r, M r :: Us x :: ss)
    | build args = args
  
  fun break (xs, C x :: ss) = break (consT (x, xs), ss)
    | break (xs, S x :: ss) = break (snocT (xs, x), ss)
    | break (xs, Uc x :: ss) = break (unconsT (xs, x), ss)
    | break (xs, Us x :: ss) = break (unsnocT (x, xs), ss)
    | break (xs, M r :: ss) = (r := xs; break (xs, ss))
    | break (xs, nil) = xs
  
  fun norm xs = break (build (xs, nil))
  fun force r =
    let val xs = norm (!r) in r := xs; xs end
  
  val empty = Empty
  fun cons (x, xs) = consT (Leaf x, xs)
  fun snoc (xs, x) = snocT (xs, Leaf x)
  
  fun uncons (Many (Leaf x :: xs, ys, zs)) = SOME (x, norm (Many (xs, ys, zs)))
    | uncons (Pure (Leaf x)) = SOME (x, Empty)
    | uncons _ = NONE
  
  fun unsnoc (Many (xs, ys, Leaf z :: zs)) = SOME (norm (Many (xs, ys, zs)), z)
    | unsnoc (Pure (Leaf x)) = SOME (Empty, x)
    | unsnoc _ = NONE
  
  (*  Recall the algorithm to find the n-th element of an indexable list:
   *  
   *  - Let p := size of the front tree.
   *  - If n = 0, then return the first element of the front tree.
   *  - If n < p, then split the front tree into subtrees.
   *  - Otherwise, discard the front tree and let n := n - p.
   *  
   *  The algorithm to find the n-th element of a deque is similar.  However, an extra complication
   *  arises from the fact that nested deques are NOT suffixes of their enclosing deques.  To work
   *  around this issue, we use the auxiliary stack ws containing the TEMPORARILY discarded suffixes
   *  as we move to the higher levels in a deque.
   *  
   *  The following quantities are always equal:
   *  
   *  - The level we are currently examining in the deque.
   *  - The length of ws.
   *  - The exponent r such that p = 2^r.
   *  
   *  When the algorithm finds the sought element, we have p = 1, hence ws = nil.  Since the only
   *  operation that shortens ws is moving (some of) its elements back into the deque, we guarantee
   *  that every element of ws will be reintegrated back into the deque at some point in time.
   *)
  
  fun loop (n, p, xs, ws) =
    case (n < p, xs, ws) of
        (_, Many (nil, xs, w), ws) => loop (n, p * base, force xs, w :: ws)
      | (true, xs, w :: ws) => loop (n, p div base, unconsT (xs, w), ws)
      | (false, Empty, w :: ws) => loop (n, p div base, wef w, ws)
      | (false, Pure _, ws) => loop (n - p, p, Empty, ws)
      | (false, Many (_ :: xs, ys, zs), ws) => loop (n - p, p, Many (xs, ys, zs), ws)
      | _ => xs
  
  fun dropL (n, xs) = loop (n, 1, xs, nil)
  
  fun loop (n, p, xs, ws) =
    case (n < p, xs, ws) of
        (_, Many (w, xs, nil), ws) => loop (n, p * base, force xs, w :: ws)
      | (true, xs, w :: ws) => loop (n, p div base, unsnocT (w, xs), ws)
      | (false, Empty, w :: ws) => loop (n, p div base, few w, ws)
      | (false, Pure _, ws) => loop (n - p, p, Empty, ws)
      | (false, Many (xs, ys, _ :: zs), ws) => loop (n - p, p, Many (xs, ys, zs), ws)
      | _ => xs
  
  fun dropR (n, xs) = loop (n, 1, xs, nil)
  
  datatype 'a step = Cut | Bump | Tree of 'a tree
  
  datatype 'a hole
    = ThinL of 'a step list
    | ThinR of 'a step list
    | FatL of 'a tree list * 'a deque ref * 'a tree list * 'a step list
    | FatR of 'a tree list * 'a deque ref * 'a tree list * 'a step list
  
  fun loop (n, p, xs, ws, ss) =
    case (n < p, xs, ws) of
        (_, Many (nil, xs, w), ws) => loop (n, p * base, force xs, w :: ws, Bump :: ss)
      | (true, Pure (Leaf x), nil) => SOME (x, ThinL ss)
      | (true, Many (Leaf x :: xs, ys, zs), nil) => SOME (x, FatL (xs, ys, zs, ss))
      | (true, xs, w :: ws) => loop (n, p div base, unconsT (xs, w), ws, Cut :: ss)
      | (false, Empty, w :: ws) => loop (n, p div base, wef w, ws, Cut :: ss)
      | (false, Pure x, ws) => loop (n - p, p, Empty, ws, Tree x :: ss)
      | (false, Many (x :: xs, ys, zs), ws) => loop (n - p, p, Many (xs, ys, zs), ws, Tree x :: ss)
      | _ => NONE
  
  fun getL (n, xs) = if n >= 0 then loop (n, 1, xs, nil, nil) else NONE
  
  fun loop (n, p, xs, ws, ss) =
    case (n < p, xs, ws) of
        (_, Many (w, xs, nil), ws) => loop (n, p * base, force xs, w :: ws, Bump :: ss)
      | (true, Pure (Leaf x), nil) => SOME (x, ThinR ss)
      | (true, Many (xs, ys, Leaf z :: zs), nil) => SOME (z, FatR (xs, ys, zs, ss))
      | (true, xs, w :: ws) => loop (n, p div base, unsnocT (w, xs), ws, Cut :: ss)
      | (false, Empty, w :: ws) => loop (n, p div base, few w, ws, Cut :: ss)
      | (false, Pure x, ws) => loop (n - p, p, Empty, ws, Tree x :: ss)
      | (false, Many (xs, ys, z :: zs), ws) => loop (n - p, p, Many (xs, ys, zs), ws, Tree z :: ss)
      | _ => NONE
  
  fun getR (n, xs) = if n >= 0 then loop (n, 1, xs, nil, nil) else NONE
  
  (*  The only operation that creates a malformed deque is a Bump, which is immediately
   *  followed by a Tree x, restoring well-formedness.  Therefore, in the first two cases,
   *  x is guaranteed to be a nonempty list.  *)
  fun loopL (Many (x, xs, w), ws, Cut :: ss) = loopL (consT (Node x, force xs), w :: ws, ss)
    | loopL (Pure x, ws, Cut :: ss) = loopL (Empty, (revT x :: nil) :: ws, ss)
    | loopL (xs, ws, Tree x :: ss) = loopL (consT (x, xs), ws, ss)
    | loopL (xs, w :: ws, Bump :: ss) = loopL (Many (nil, ref xs, w), ws, ss)
    | loopL (xs, _, _) = xs
  
  (*  The only operation that creates a malformed deque is a Bump, which is immediately
   *  followed by a Tree x, restoring well-formedness.  Therefore, in the first two cases,
   *  x is guaranteed to be a nonempty list.  *)
  fun loopR (Many (w, xs, x), ws, Cut :: ss) = loopR (snocT (force xs, Node x), w :: ws, ss)
    | loopR (Pure x, ws, Cut :: ss) = loopR (Empty, (x :: nil) :: ws, ss)
    | loopR (xs, ws, Tree x :: ss) = loopR (snocT (xs, x), ws, ss)
    | loopR (xs, w :: ws, Bump :: ss) = loopR (Many (w, ref xs, nil), ws, ss)
    | loopR (xs, _, _) = xs
  
  fun set (x, ThinL ss) = loopL (Pure (Leaf x), nil, ss)
    | set (x, ThinR ss) = loopR (Pure (Leaf x), nil, ss)
    | set (x, FatL (xs, ys, zs, ss)) = loopL (Many (Leaf x :: xs, ys, zs), nil, ss)
    | set (z, FatR (xs, ys, zs, ss)) = loopR (Many (xs, ys, Leaf z :: zs), nil, ss)
end
