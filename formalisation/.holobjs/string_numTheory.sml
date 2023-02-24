structure string_numTheory :> string_numTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading string_numTheory ... "
    else ()
  
  open Type Term Thm
  local open Pf0DrvTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "string_num"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formalisation/string_numTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op n2s_def_primitive _ = ()
  val op n2s_def_primitive = TDB.find "n2s_def_primitive"
  fun op s2n_def _ = () val op s2n_def = TDB.find "s2n_def"
  fun op n2nsum_def _ = () val op n2nsum_def = TDB.find "n2nsum_def"
  fun op nsum2n_def _ = () val op nsum2n_def = TDB.find "nsum2n_def"
  fun op s2ssum_def _ = () val op s2ssum_def = TDB.find "s2ssum_def"
  fun op ssum2s_def _ = () val op ssum2s_def = TDB.find "ssum2s_def"
  fun op n2s_ind _ = () val op n2s_ind = TDB.find "n2s_ind"
  fun op n2s_def _ = () val op n2s_def = TDB.find "n2s_def"
  fun op s2n_n2s _ = () val op s2n_n2s = TDB.find "s2n_n2s"
  fun op n2s_s2n _ = () val op n2s_s2n = TDB.find "n2s_s2n"
  fun op n2s_11 _ = () val op n2s_11 = TDB.find "n2s_11"
  fun op s2n_11 _ = () val op s2n_11 = TDB.find "s2n_11"
  fun op n2s_onto _ = () val op n2s_onto = TDB.find "n2s_onto"
  fun op s2n_onto _ = () val op s2n_onto = TDB.find "s2n_onto"
  fun op n2nsum_nsum2n _ = ()
  val op n2nsum_nsum2n = TDB.find "n2nsum_nsum2n"
  fun op nsum2n_n2nsum _ = ()
  val op nsum2n_n2nsum = TDB.find "nsum2n_n2nsum"
  fun op s2ssum_ssum2s _ = ()
  val op s2ssum_ssum2s = TDB.find "s2ssum_ssum2s"
  fun op ssum2s_s2ssum _ = ()
  val op ssum2s_s2ssum = TDB.find "ssum2s_s2ssum"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "string_num"

val string_num_grammars = valOf (Parse.grammarDB {thyname = "string_num"})
end
