signature STRONGLY_CONNECTED =
sig
  type graph = int list vector
  type stream
  
  val sccs : graph * int list -> stream
  val next : stream -> int list
end
