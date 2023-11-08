
fun curry f x y = f (x,y);

fun read_all_lines filename =
  let
    val f = TextIO.openIn(filename)
    fun read_rest () =
      case TextIO.inputLine(f) of
        NONE => []
      | SOME line => line :: read_rest ()
    val all_lines = read_rest ()
    val _ = TextIO.closeIn f
  in SOME all_lines end
  handle e => NONE;

fun write_file filename lines = let
  val f = TextIO.openOut(filename)
  val _ = List.app (curry TextIO.output f) lines
  val _ = TextIO.closeOut f
  in () end;

val old_suffix = " " ^ implode (map chr [226, 136, 167, 10]);
val old_prefix = "["
val new_suffix = "\n"

fun process [] = []
  | process [l1] = [l1]
  | process (l1::l2::[]) = l1::l2::[]
  | process (l1::l2::l3::lines) =
      if String.isSuffix old_suffix l1 andalso
         (String.isPrefix old_prefix l2 orelse
          (String.isPrefix old_prefix l3 andalso l2 = "\n"))
      then
        (String.substring(l1,0,String.size(l1) - String.size(old_suffix)) ^ new_suffix)
        :: process (l2::l3::lines)
      else
        l1 :: process (l2::l3::lines);

fun fix_file filename =
  case read_all_lines filename of
    NONE => ()
  | SOME lines => write_file filename (process lines);

fun main () =
  let
    val args = CommandLine.arguments ()
  in
    List.app fix_file args
  end;
