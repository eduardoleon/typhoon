functor ImplicitKaryList (val base : int) :> INDEXABLE_LIST =
struct
  open Unrank
  
  datatype 'a tree = Leaf of 'a | Node of 'a tree list
  
  datatype 'a frame
    = Empty
    | Cons of 'a tree * 'a frame ref
    | Many of 'a tree list * 'a frame ref
  
  fun many (x, xs, ys) = Many (x, ref (Many (xs, ys)))
  
  fun consF (ys, zs) =
    case halve (base, ys) of
        NONE => Many (ys, zs)
      | SOME (xs, ys) => Many (xs, ref (Cons (Node ys, zs)))
  
  fun consT (x, Many (xs, ys)) = consF (x :: xs, ys)
    | consT (x, _) = Many (x :: nil, ref Empty)
  
  fun unconsT (Many (Node x :: xs, ys)) = many (x, xs, ys)
    | unconsT _ = Empty
  
  datatype 'a step = C of 'a tree | Uc | M of 'a frame ref
  
  fun build (Cons (x, r), ss) = build (!r, M r :: C x :: ss)
    | build (Many (nil, r), ss) = build (!r, M r :: Uc :: ss)
    | build args = args
  
  fun break (xs, C x :: ss) = break (consT (x, xs), ss)
    | break (xs, Uc :: ss) = break (unconsT xs, ss)
    | break (xs, M r :: ss) = (r := xs; break (xs, ss))
    | break (xs, nil) = xs
  
  fun norm xs = break (build (xs, nil))
  fun force r =
    let val xs = norm (!r) in r := xs; xs end
  
  val empty = Empty
  fun cons (x, xs) = consT (Leaf x, xs)
  fun uncons (Many (Leaf x :: xs, ys)) = SOME (x, norm (Many (xs, ys)))
    | uncons _ = NONE
  
  datatype 'a step = Cut | Bump | Tree of 'a tree
  
  type 'a hole = 'a tree list * 'a frame ref * 'a step list
  type 'a list = 'a frame
  
  fun loop (n, p, xs) =
    case (n < p, xs) of
        (_, Many (nil, xs)) => loop (n, p * base, force xs)
      | (true, Many (Node x :: xs, ys)) => loop (n, p div base, many (x, xs, ys))
      | (false, Many (_ :: xs, ys)) => loop (n - p, p, Many (xs, ys))
      | _ => xs
  
  fun drop (n, xs) = loop (n, 1, xs)
  
  fun loop (n, p, xs, ss) = 
    case (n < p, xs) of
        (_, Many (nil, xs)) => loop (n, p * base, force xs, Bump :: ss)
      | (true, Many (Leaf x :: xs, ys)) => SOME (x, (xs, ys, ss))
      | (true, Many (Node x :: xs, ys)) => loop (n, p div base, many (x, xs, ys), Cut :: ss)
      | (false, Many (x :: xs, ys)) => loop (n - p, p, Many (xs, ys), Tree x :: ss)
      | _ => NONE
  
  fun get (n, xs) = if n >= 0 then loop (n, 1, xs, nil) else NONE
  
  fun loop (Many (x, ref (Many (xs, ys))), Cut :: ss) = loop (Many (Node x :: xs, ys), ss)
    | loop (Many (xs, ys), Tree x :: ss) = loop (Many (x :: xs, ys), ss)
    | loop (xs, Bump :: ss) = loop (Many (nil, ref xs), ss)
    | loop (xs, _) = xs
  
  fun set (x, (xs, ys, ss)) = loop (Many (Leaf x :: xs, ys), ss)
  fun trunc (xs, ys, _) = norm (Many (xs, ys))
end
