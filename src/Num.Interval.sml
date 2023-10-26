signature INTERVAL =
sig
  val cutoff : int * int list -> int
end

structure Interval : INTERVAL =
struct
  fun loop (n, _, nil) = n
    | loop (n, x, y :: xs) = if x < y then n else loop (n + 1, x, xs)
  
  fun cutoff (x, xs) = loop (0, x, xs)
end
