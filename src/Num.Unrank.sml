signature UNRANK =
sig
  val halve : int * 'a list -> ('a list * 'a list) option
  val split : 'a list -> 'a list * 'a list
end

structure Unrank : UNRANK =
struct
  fun loop (0, xs, ys, nil) = SOME (rev xs, ys)
    | loop (n, xs, y :: ys, _ :: _ :: zs) = loop (n - 1, y :: xs, ys, zs)
    | loop _ = NONE
  
  fun halve (n, xs) = loop (n, nil, xs, xs)
  
  fun loop (xs, y :: ys, _ :: _ :: zs) = loop (y :: xs, ys, zs)
    | loop (xs, ys, _) = (rev xs, ys)
  
  fun split xs = loop (nil, xs, xs)
end
