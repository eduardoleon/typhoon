signature COMPARE =
sig
  type 'a compare = 'a * 'a -> bool
  
  val min : 'a compare -> 'a * 'a -> 'a
  val max : 'a compare -> 'a * 'a -> 'a
  val swap : 'a compare -> 'a * 'a -> 'a * 'a
  val bubble : ('a * 'a -> 'a * 'a) -> 'a * 'a list -> 'a * 'a list
end

structure Compare : COMPARE =
struct
  type 'a compare = 'a * 'a -> bool
  
  fun min f (x, y) = if f (x, y) then x else y
  fun max f (x, y) = if f (x, y) then y else x
  fun swap f (x, y) = if f (x, y) then (x, y) else (y, x)
  
  fun loop f (x, xs, nil) = (x, xs)
    | loop f (x, xs, y :: ys) =
      let val (x, y) = f (x, y)
      in loop f (x, y :: xs, ys) end
  
  fun bubble f (x, xs) = loop f (x, nil, xs)
end
