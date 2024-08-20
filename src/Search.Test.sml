signature SEARCH_TEST =
sig
  val ascTest : int * int -> bool list
  val descTest : int * int -> bool list
end

functor SearchTest (T : SEARCH_TREE) : SEARCH_TEST =
struct
  open T
  
  fun pull (0, xs, ys) = (xs, ys)
    | pull (n, xs, ys) =
      case root xs of
          Leaf _ => (xs, ys)
        | Node (x, xs) => pull (n - 1, delete xs, x :: ys)
  
  fun loop (x, Leaf xs) = insert (x, xs)
    | loop (x, Node xs) =
      if x <= #1 xs then loop (x, left xs) else loop (x, right xs)
  
  fun push (xs, y :: ys) = push (loop (y, root xs), ys)
    | push (xs, nil) = xs
  
  fun ascTest (n, k) =
    let
      val xs = List.tabulate (n, fn n => n)
      val ys = fromAsc xs
      val zs = pull (k, ys, nil)
      val ws = push zs
    in
      [ xs = toAsc ws
      , height ys >= 0
      , height (#1 zs) >= 0
      , height ws >= 0
      ]
    end
  
  fun descTest (n, k) =
    let
      val xs = List.tabulate (n, fn n => ~n)
      val ys = fromDesc xs
      val zs = pull (k, ys, nil)
      val ws = push zs
    in
      [ xs = toDesc ws
      , height ys >= 0
      , height (#1 zs) >= 0
      , height ws >= 0
      ]
    end
end
