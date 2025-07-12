functor SegmentedBinomialHeap (E : ORDERED) :> HEAP where type elem = E.elem =
struct
  open E
  
  datatype 'a tree = Tree of 'a * 'a tree list
  
  datatype 'a step
    = Zero
    | One of 'a tree list
    | Two of 'a tree * 'a tree
  
  fun tree (x, One xs :: ys) = One (x :: xs) :: ys
    | tree (x, xs) = One (x :: nil) :: xs
  
  fun segm (nil, ys) = ys
    | segm (xs, ys) = One xs :: ys
  
  datatype heap = ::: of elem * heap step list
  
  fun pure x = x ::: nil
  fun head (x ::: _) = x
  fun comp (x ::: _, y ::: _) = x <= y
  
  fun zero x = Tree (x, nil)
  fun succ (ys as Tree (x, xss), xs as Tree (y, yss)) =
    if comp (x, y) then Tree (x, xs :: xss) else Tree (y, ys :: yss)
  
  fun cons (x, One (y :: ys) :: xs) = Two (x, y) :: segm (ys, xs)
    | cons (x, Zero :: xs) = tree (x, xs)
    | cons (x, _) = One (x :: nil) :: nil
  
  fun fix (One xs :: Two y :: ys) = One xs :: Zero :: cons (succ y, ys)
    | fix (Two x :: xs) = Zero :: cons (succ x, xs)
    | fix xs = xs
  
  fun link (ys as x ::: xss, xs as y ::: yss) =
    if x <= y then x ::: fix (cons (zero xs, xss))
              else y ::: fix (cons (zero ys, yss))
  
  (*  To discard the minimum element of a heap, we must turn the heap's tail into
   *  another heap.  This operation has four phases.
   *)
  
  (*  PHASE 1:  Find the minimum tree and remove it from the tail.  This splits
   *  the rest of the tail into a prefix and a suffix.
   *)
  fun focus (One (x :: xs) :: ys, zs) = SOME (x, segm (xs, ys), zs)
    | focus (Zero :: xs, ys) = focus (fix xs, NONE :: ys)
    | focus _ = NONE
  
  fun root (Tree (x, _), _, _) = x
  fun next (x, xs, ys) = focus (xs, SOME x :: ys)
  
  fun select (xs, NONE) = xs
    | select (xs, SOME ys) =
      if comp (root xs, root ys) then select (xs, next ys)
                                 else select (ys, next ys)
  
  (*  PHASE 2:  Split the minimum tree into root and children, then the root into
   *  head and tail, and then the tail into a prefix and a suffix.  This prefix
   *  must be exactly as long as the prefix from phase 1.
   *)
  fun split1 (_ :: ws, One (x :: xs) :: ys, zs) = split1 (ws, segm (xs, ys), SOME x :: zs)
    | split1 (_ :: ws, Zero :: xs, ys) = split1 (ws, fix xs, NONE :: ys)
    | split1 (_ :: ws, _, xs) = split1 (ws, nil, NONE :: xs)
    | split1 (nil, xs, ys) = (xs, ys)
  
  (*  PHASE 3:  Split the longer suffix into a prefix and a residue.  This prefix
   *  must be as long as the shorter suffix.
   *)
  fun uncons (One (x :: xs) :: ys) = SOME (SOME x, segm (xs, ys))
    | uncons (Zero :: xs) = SOME (NONE, fix xs)
    | uncons _ = NONE
  
  fun splits (xs, ys, zs, ws) =
    case (uncons xs, uncons zs) of
        (_, NONE) => (xs, ys, ws)
      | (NONE, _) => (zs, ys, ws)
      | (SOME (x, xs), SOME (z, zs)) => splits (xs, x :: ys, zs, z :: ws)
  
  fun split2 (nil, ys) = (ys, nil, nil)
    | split2 (xs, ys) = splits (Zero :: xs, nil, ys, nil)
  
  (*  PHASE 4:  Move everything into the residue.  *)
  fun NONE @ xs = xs
    | (SOME x) @ xs = fix (cons (x, xs))
  
  fun merge2 (xs, y :: ys, z :: zs) = merge2 (y @ z @ Zero :: xs, ys, zs)
    | merge2 (xs, _, _) = xs
  
  fun merge3 (xs, y :: ys, z :: zs, w :: ws) = merge3 (y @ z @ tree (w, xs), ys, zs, ws)
    | merge3 (xs, _, _, _) = xs
  
  (*  Finally, we put everything together.  *)
  fun tail (_ ::: xs) =
    case focus (xs, nil) of
        NONE => NONE
      | SOME xs =>
        let
          (*  Phase 1  *)
          val (x, xs1, ys1) = select (xs, next xs)
          
          (*  Phase 2 and 3  *)
          val Tree (x ::: xs, ys) = x
          val (xs2, ys2) = split1 (ys, xs, nil)
          val (xs, zs1, zs2) = split2 (xs1, xs2)
          
          (*  Phase 4  *)
          val xs = merge2 (xs, zs1, zs2)
          val xs = merge3 (xs, ys1, ys2, ys)
        in
          SOME (x ::: xs)
        end
end
