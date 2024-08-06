functor SimpleCatenableDeque (D : ATOM_DEQUE) :> BULK_DEQUE =
struct
  open D
  
  type 'a finger = 'a * 'a deque * 'a
  
  fun consF (x, (y, a, z)) = (x, cons (y, a), z)
  fun snocF ((x, a, y), z) = (x, snoc (a, y), z)
  
  datatype 'a frame
    = Empty
    | Pure of 'a
    | Some of 'a finger
    | Cons of 'a finger * 'a frame ref
    | Snoc of 'a frame ref * 'a finger
    | Uncons of 'a * 'a frame ref * 'a finger
    | Unsnoc of 'a finger * 'a frame ref * 'a
    | Link of 'a frame ref * 'a finger * 'a finger * 'a frame ref
    | Many of 'a finger * 'a frame ref * 'a finger
  
  fun consT (x, Many (a, xs, b)) = Many (consF (x, a), xs, b)
    | consT (x, Some a) = Some (consF (x, a))
    | consT (x, Pure y) = Some (x, empty, y)
    | consT (x, _) = Pure x
  
  fun snocT (Many (a, xs, b), x) = Many (a, xs, snocF (b, x))
    | snocT (Some a, x) = Some (snocF (a, x))
    | snocT (Pure x, y) = Some (x, empty, y)
    | snocT (_, x) = Pure x
  
  fun unconsM ((x, a, z), xs, b) =
    case uncons a of
        SOME (y, a) => (x, Many ((y, a, z), xs, b))
      | NONE => (x, Uncons (z, xs, b))
  
  fun unsnocM (a, xs, (x, b, z)) =
    case unsnoc b of
        SOME (b, y) => (Many (a, xs, (x, b, y)), z)
      | NONE => (Unsnoc (a, xs, x), z)
  
  fun unconsS (x, a, z) =
    case uncons a of
        SOME (y, a) => (x, Some (y, a, z))
      | NONE => (x, Pure z)
  
  fun unsnocS (x, a, z) =
    case unsnoc a of
        SOME (a, y) => (Some (x, a, y), z)
      | NONE => (Pure x, z)
  
  fun unconsT (Many xs) = SOME (unconsM xs)
    | unconsT (Some xs) = SOME (unconsS xs)
    | unconsT (Pure x) = SOME (x, Empty)
    | unconsT _ = NONE
  
  fun unsnocT (Many xs) = SOME (unsnocM xs)
    | unsnocT (Some xs) = SOME (unsnocS xs)
    | unsnocT (Pure x) = SOME (Empty, x)
    | unsnocT _ = NONE
  
  datatype 'a tree = Leaf of 'a | Node of 'a tree finger
  
  type 'a deque = 'a tree frame
  
  val empty = Empty
  fun cons (x, xs) = consT (Leaf x, xs)
  fun snoc (xs, x) = snocT (xs, Leaf x)
  
  fun uncons (x, xs, b) =
    case unconsT xs of
        SOME (Node a, xs) => Many (consF (x, a), ref xs, b)
      | _ => Some (consF (x, b))
  
  fun unsnoc (a, xs, x) =
    case unsnocT xs of
        SOME (xs, Node b) => Many (a, ref xs, snocF (b, x))
      | _ => Some (snocF (a, x))
  
  fun link (Many (a, xs, b), Many (c, ys, d)) = Many (a, ref (Link (xs, b, c, ys)), d)
    | link (Many (a, xs, b), Some c) = Many (a, ref (Snoc (xs, b)), c)
    | link (Some a, Many (b, xs, c)) = Many (a, ref (Cons (b, xs)), c)
    | link (Some a, Some b) = Many (a, ref Empty, b)
    | link (Pure x, xs) = consT (x, xs)
    | link (xs, Pure x) = snocT (xs, x)
    | link (Empty, xs) = xs
    | link (xs, _) = xs
  
  datatype 'a step
    = C of 'a finger
    | S of 'a finger
    | Uc of 'a * 'a finger
    | Us of 'a finger * 'a
    | L of 'a finger * 'a frame ref
    | R of 'a frame
    | M of 'a frame ref
  
  fun force (Cons (x, r), ss) = force (!r, M r :: C x :: ss)
    | force (Snoc (r, x), ss) = force (!r, M r :: S x :: ss)
    | force (Uncons (x, r, y), ss) = force (!r, M r :: Uc (x, y) :: ss)
    | force (Unsnoc (x, r, y), ss) = force (!r, M r :: Us (x, y) :: ss)
    | force (Link (r, x, y, s), ss) = force (!r, M r :: S x :: L (y, s) :: ss)
    | force (xs, C x :: ss) = force (consT (Node x, xs), ss)
    | force (xs, S x :: ss) = force (snocT (xs, Node x), ss)
    | force (xs, Uc (x, y) :: ss) = force (uncons (x, xs, y), ss)
    | force (xs, Us (x, y) :: ss) = force (unsnoc (x, xs, y), ss)
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
