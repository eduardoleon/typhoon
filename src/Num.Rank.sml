signature RANK =
sig
  type 'a rank = int * 'a
  type 'a many = int * 'a * 'a list * 'a rank list
  type 'a focus = int * 'a * 'a rank list * 'a rank list
  
  val untag : int * int * 'a * 'a rank list -> 'a many option
  val untag' : int * 'a rank list -> 'a many option
  
  val retag : int * 'a list * 'a rank list -> 'a rank list
  val retag' : int * 'a list list -> 'a rank list
  
  val collect : 'a rank list * 'a rank list -> 'a rank list * 'a rank list
  
  val first : 'a rank list -> 'a focus option
  val next : 'a focus -> 'a focus option
  val locate : 'a Compare.compare -> 'a focus -> 'a focus
end

structure Rank : RANK =
struct
  type 'a rank = int * 'a
  type 'a many = int * 'a * 'a list * 'a rank list
  type 'a focus = int * 'a * 'a rank list * 'a rank list
  
  fun loop (1, p, x, xs, ys) = SOME (p, x, xs, ys)
    | loop (n, p, x, xs, (q, y) :: ys) =
      if p = q then loop (n - 1, p, y, x :: xs, ys) else NONE
    | loop _ = NONE
  
  fun untag (n, p, x, xs) = loop (n, p, x, nil, xs)
  fun untag' (n, (p, x) :: xs) = loop (n, p, x, nil, xs)
    | untag' _ = NONE
  
  fun retag (_, nil, ys) = ys
    | retag (p, x :: xs, ys) = retag (p, xs, (p, x) :: ys)
  
  fun loop (_, nil, ys) = ys
    | loop (p, x :: xs, ys) = loop (p - 1, xs, retag (p, x, ys))
  
  fun retag' (p, xs) = loop (p, xs, nil)
  
  fun loop (xs, nil, zs) = (xs, zs)
    | loop (nil, ys, zs) = (ys, zs)
    | loop (xxs as (p, x) :: xs, yys as (q, y) :: ys, zs) =
      if p <= q then loop (xs, yys, (p, x) :: zs)
                else loop (xxs, ys, (q, y) :: zs)
  
  fun collect (xs, ys) = loop (xs, ys, nil)
  
  fun focus ((p, x) :: xs, ys) = SOME (p, x, xs, ys)
    | focus _ = NONE
  
  fun first xs = focus (xs, nil)
  fun next (p, x, xs, ys) = focus (xs, (p, x) :: ys)
  
  fun loop _ (xs, NONE) = xs
    | loop f (xs, SOME ys) = loop f (f (xs, ys), next ys)
  
  fun locate f xs =
    let fun g (xs, ys) = f (#2 xs, #2 ys)
    in loop (Compare.min g) (xs, next xs) end
end
