functor ImplicitCatenableDeque (D : ATOM_DEQUE) :> BULK_DEQUE =
struct
  open D
  
  type 'a finger = 'a * 'a deque * 'a
  
  fun pair (x, y) = (x, empty, y)
  fun consF (x, (y, a, z)) = (x, cons (y, a), z)
  fun snocF ((x, a, y), z) = (x, snoc (a, y), z)
  
  datatype 'a frame
    = Empty
    | One of 'a
    | Two of 'a * 'a
    | Three of 'a * 'a * 'a
    | Some of 'a * 'a finger * 'a
    | Cons of 'a * 'a frame ref
    | Snoc of 'a frame ref * 'a
    | Link of 'a frame ref * 'a * 'a frame ref
    | UnconsR of 'a * 'a finger * 'a frame ref * 'a finger * 'a
    | UnsnocL of 'a * 'a finger * 'a frame ref * 'a finger * 'a
    | UnconsL of 'a * 'a * 'a frame ref * 'a finger * 'a frame ref * 'a finger * 'a
    | UnsnocR of 'a * 'a finger * 'a frame ref * 'a finger * 'a frame ref * 'a * 'a
    | Many of 'a * 'a finger * 'a frame ref * 'a finger * 'a frame ref * 'a finger * 'a
  
  fun four (x, y, z, w) = Some (x, pair (y, z), w)
  fun few (x, a, w) =
    case uncons a of
        NONE => Two (x, w)
      | SOME (y, a) =>
        case unsnoc a of
            NONE => Three (x, y, w)
          | SOME (a, z) => Some (x, (y, a, z), w)
  
  fun consT (x, Many (y, a, ys, b, zs, c, z)) = Many (x, consF (y, a), ys, b, zs, c, z)
    | consT (x, Some (y, a, z)) = Some (x, consF (y, a), z)
    | consT (x, Three (y, z, w)) = four (x, y, z, w)
    | consT (x, Two (y, z)) = Three (x, y, z)
    | consT (x, One y) = Two (x, y)
    | consT (x, _) = One x
  
  fun snocT (Many (x, a, xs, b, ys, c, y), z) = Many (x, a, xs, b, ys, snocF (c, y), z)
    | snocT (Some (x, a, y), z) = Some (x, snocF (a, y), z)
    | snocT (Three (x, y, z), w) = four (x, y, z, w)
    | snocT (Two (x, y), z) = Three (x, y, z)
    | snocT (One x, y) = Two (x, y)
    | snocT (_, x) = One x
  
  fun unconsM (x, (y, a, v), xs, b, ys, c, w) =
    case uncons a of
        SOME (z, a) => (x, Many (y, (z, a, v), xs, b, ys, c, w))
      | NONE => (x, UnconsL (y, v, xs, b, ys, c, w))
  
  fun unsnocM (x, a, xs, b, ys, (y, c, v), w) =
    case unsnoc c of
        SOME (c, z) => (Many (x, a, xs, b, ys, (y, c, z), v), w)
      | NONE => (UnsnocR (x, a, xs, b, ys, y, v), w)
  
  fun unconsS (x, (y, a, v), w) =
    case uncons a of
        SOME (z, a) => (x, Some (y, (z, a, v), w))
      | NONE => (x, Three (y, v, w))
  
  fun unsnocS (x, (y, a, v), w) =
    case unsnoc a of
        SOME (a, z) => (Some (x, (y, a, z), v), w)
      | NONE => (Three (x, y, v), w)
  
  fun unconsT (Many xs) = SOME (unconsM xs)
    | unconsT (Some xs) = SOME (unconsS xs)
    | unconsT (Three (x, y, z)) = SOME (x, Two (y, z))
    | unconsT (Two (x, y)) = SOME (x, One y)
    | unconsT (One x) = SOME (x, Empty)
    | unconsT _ = NONE
  
  fun unsnocT (Many xs) = SOME (unsnocM xs)
    | unsnocT (Some xs) = SOME (unsnocS xs)
    | unsnocT (Three (x, y, z)) = SOME (Two (x, y), z)
    | unsnocT (Two (x, y)) = SOME (One x, y)
    | unsnocT (One x) = SOME (Empty, x)
    | unsnocT _ = NONE
  
  datatype 'a tree
    = Leaf of 'a
    | Thin of 'a tree finger
    | Fat of 'a tree finger * 'a deque ref * 'a tree finger
  
  withtype 'a deque = 'a tree frame
  
  val empty = Empty
  fun cons (x, xs) = consT (Leaf x, xs)
  fun snoc (xs, x) = snocT (xs, Leaf x)
  
  fun shift (a, x, y) = Thin (snocF (snocF (a, x), y))
  fun tfihs (x, y, a) = Thin (consF (x, consF (y, a)))
  fun link (Many (x, a, xs, b, ys, c, y), Many (z, d, zs, e, ws, f, w)) =
      let val xys = Snoc (xs, Fat (b, ys, c))
          val zws = Cons (Fat (d, zs, e), ws)
      in Many (x, a, ref xys, pair (y, z), ref zws, f, w) end
    | link (Many (x, a, xs, b, ys, c, y), Some (z, d, w)) =
      let val ys = Snoc (ys, shift (c, y, z))
      in Many (x, a, xs, b, ref ys, d, w) end
    | link (Some (x, a, y), Many (z, b, zs, c, ws, d, w)) =
      let val zs = Cons (tfihs (y, z, b), zs)
      in Many (x, a, ref zs, c, ws, d, w) end
    | link (Some (x, a, y), Some (z, b, w)) =
      let val xs = ref Empty
      in Many (x, a, xs, pair (y, z), xs, b, w) end
    | link (Three (x, y, z), xs) = link (Two (x, y), consT (z, xs))
    | link (xs, Three (x, y, z)) = link (snocT (xs, x), Two (y, z))
    | link (Two (x, y), xs) = link (One x, consT (y, xs))
    | link (xs, Two (x, y)) = link (snocT (xs, x), One y)
    | link (One x, xs) = consT (x, xs)
    | link (xs, One x) = snocT (xs, x)
    | link (Empty, xs) = xs
    | link (xs, _) = xs
  
  fun unconsL (x, y, ys, c, zs, d, z) =
    case unconsT ys of
        SOME (Fat (a, xs, b), ys) =>
        let val ys = Link (xs, Thin b, ref ys)
        in Many (x, consF (y, a), ref ys, c, zs, d, z) end
      | SOME (Thin a, ys) => Many (x, consF (y, a), ref ys, c, zs, d, z)
      | _ => UnconsR (x, consF (y, c), zs, d, z)
  
  fun unsnocR (x, a, xs, b, ys, y, z) =
    case unsnocT ys of
        SOME (ys, Fat (c, zs, d)) =>
        let val ys = Link (ref ys, Thin c, zs)
        in Many (x, a, xs, b, ref ys, snocF (d, y), z) end
      | SOME (ys, Thin c) => Many (x, a, xs, b, ref ys, snocF (c, y), z)
      | _ => UnsnocL (x, a, xs, snocF (b, y), z)
  
  fun unconsR (x, a, ys, d, y) =
    case unconsT ys of
        SOME (Fat (b, xs, c), ys) =>
        let val xs = Cons (Thin b, xs)
        in Many (x, a, ref xs, c, ref ys, d, y) end
      | SOME (Thin b, ys) => Many (x, a, ref Empty, b, ref ys, d, y)
      | _ => link (consT (x, few a), snocT (few d, y))
  
  fun unsnocL (x, a, xs, d, y) =
    case unsnocT xs of
        SOME (xs, Fat (b, ys, c)) =>
        let val ys = Snoc (ys, Thin c)
        in Many (x, a, ref xs, b, ref ys, d, y) end
      | SOME (xs, Thin b) => Many (x, a, ref xs, b, ref Empty, d, y)
      | _ => link (consT (x, few a), snocT (few d, y))
  
  datatype 'a step
    = C of 'a
    | S of 'a
    | UcR of 'a * 'a finger * 'a finger * 'a
    | UsL of 'a * 'a finger * 'a finger * 'a
    | UcL of 'a * 'a * 'a finger * 'a frame ref * 'a finger * 'a
    | UsR of 'a * 'a finger * 'a frame ref * 'a finger * 'a * 'a
    | L of 'a * 'a frame ref
    | R of 'a frame
    | M of 'a frame ref
  
  fun force (Cons (x, r), ss) = force (!r, M r :: C x :: ss)
    | force (Snoc (r, x), ss) = force (!r, M r :: S x :: ss)
    | force (UnconsR (x, a, r, b, y), ss) = force (!r, M r :: UcR (x, a, b, y) :: ss)
    | force (UnsnocL (x, a, r, b, y), ss) = force (!r, M r :: UsL (x, a, b, y) :: ss)
    | force (UnconsL (x, y, r, a, xs, b, z), ss) = force (!r, M r :: UcL (x, y, a, xs, b, z) :: ss)
    | force (UnsnocR (x, a, xs, b, r, y, z), ss) = force (!r, M r :: UsR (x, a, xs, b, y, z) :: ss)
    | force (Link (r, x, s), ss) = force (!r, M r :: L (x, s) :: ss)
    | force (xs, C x :: ss) = force (consT (x, xs), ss)
    | force (xs, S x :: ss) = force (snocT (xs, x), ss)
    | force (xs, UcR (x, a, b, y) :: ss) = force (unconsR (x, a, xs, b, y), ss)
    | force (xs, UsL (x, a, b, y) :: ss) = force (unsnocL (x, a, xs, b, y), ss)
    | force (xs, UcL (x, y, a, ys, b, z) :: ss) = force (unconsL (x, y, xs, a, ys, b, z), ss)
    | force (ys, UsR (x, a, xs, b, y, z) :: ss) = force (unsnocR (x, a, xs, b, ys, y, z), ss)
    | force (xs, L (x, r) :: ss) = force (!r, M r :: C x :: R xs :: ss)
    | force (ys, R xs :: ss) = force (link (xs, ys), ss)
    | force (xs, M r :: ss) = (r := xs; force (xs, ss))
    | force (xs, nil) = xs
  
  fun uncons xs =
    case unconsT xs of
        SOME (Leaf x, xs) => SOME (x, force (xs, nil))
      | _ => NONE
  
  fun unsnoc xs =
    case unsnocT xs of
        SOME (xs, Leaf x) => SOME (force (xs, nil), x)
      | _ => NONE
end
