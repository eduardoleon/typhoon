signature HEAP_TEST =
sig
  val grayTest : int -> bool list
end

functor HeapTest (H : HEAP where type elem = int) : HEAP_TEST =
struct
  open Word
  
  infix 5 << >>
  
  fun gray n = xorb (n, n >> 0wx1)
  
  fun merge (_, x :: nil) = x
    | merge (xs, x :: y :: ys) = merge (H.link (x, y) :: xs, ys)
    | merge (xs, _) = merge (nil, xs)
  
  fun flatten (xs, NONE) = xs
    | flatten (xs, SOME ys) = flatten (H.head ys :: xs, H.tail ys)
  
  fun grayTest k =
    let
      val n = toInt (0wx1 << fromInt k)
      val xs = List.tabulate (n, fn n => n)
      val ys = List.tabulate (n, fn n => H.pure (toInt (gray (fromInt n))))
      val zs = merge (nil, ys)
      val ws = flatten (nil, SOME zs)
    in
      [xs = rev ws]
    end
end
