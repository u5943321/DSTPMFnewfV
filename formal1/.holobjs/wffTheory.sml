structure wffTheory :> wffTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading wffTheory ... "
    else ()
  
  open Type Term Thm
  local open wfgenl1Theory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "wff"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFnewfV/formal/wffTheory.dat")
    fun find s = HOLdict.find (thydata,s)
  end
  
  fun op wffVmap_def _ = () val op wffVmap_def = TDB.find "wffVmap_def"
  fun op wff_def _ = () val op wff_def = TDB.find "wff_def"
  fun op wff_frename _ = () val op wff_frename = TDB.find "wff_frename"
  fun op wff_wfcod_cvmap_ffv _ = ()
  val op wff_wfcod_cvmap_ffv = TDB.find "wff_wfcod_cvmap_ffv"
  fun op wff_FALLL_no_vbound _ = ()
  val op wff_FALLL_no_vbound = TDB.find "wff_FALLL_no_vbound"
  fun op wff_fVar_subst_lemma _ = ()
  val op wff_fVar_subst_lemma = TDB.find "wff_fVar_subst_lemma"
  fun op wff_spec _ = () val op wff_spec = TDB.find "wff_spec"
  fun op wff_no_vbound _ = ()
  val op wff_no_vbound = TDB.find "wff_no_vbound"
  fun op wff_fbounds _ = () val op wff_fbounds = TDB.find "wff_fbounds"
  fun op wff_wfs _ = () val op wff_wfs = TDB.find "wff_wfs"
  fun op wff_FALL _ = () val op wff_FALL = TDB.find "wff_FALL"
  fun op wff_fVar _ = () val op wff_fVar = TDB.find "wff_fVar"
  fun op wfcod_rnmap_ffv _ = ()
  val op wfcod_rnmap_ffv = TDB.find "wfcod_rnmap_ffv"
  fun op wff_finst _ = () val op wff_finst = TDB.find "wff_finst"
  fun op wff_EQ _ = () val op wff_EQ = TDB.find "wff_EQ"
  fun op wff_False _ = () val op wff_False = TDB.find "wff_False"
  fun op wff_cases _ = () val op wff_cases = TDB.find "wff_cases"
  fun op wff_strongind _ = ()
  val op wff_strongind = TDB.find "wff_strongind"
  fun op wff_ind _ = () val op wff_ind = TDB.find "wff_ind"
  fun op wff_rules _ = () val op wff_rules = TDB.find "wff_rules"
  fun op wff_Pred _ = () val op wff_Pred = TDB.find "wff_Pred"
  fun op wff_IMP _ = () val op wff_IMP = TDB.find "wff_IMP"
  fun op fVmap_no_bound_lemma _ = ()
  val op fVmap_no_bound_lemma = TDB.find "fVmap_no_bound_lemma"
  fun op wffVmap_fVmap_rename _ = ()
  val op wffVmap_fVmap_rename = TDB.find "wffVmap_fVmap_rename"
  fun op wffVmap_no_vbound _ = ()
  val op wffVmap_no_vbound = TDB.find "wffVmap_no_vbound"
  fun op wff_fVinst _ = () val op wff_fVinst = TDB.find "wff_fVinst"
  fun op mk_FALLL_fVar_wff _ = ()
  val op mk_FALLL_fVar_wff = TDB.find "mk_FALLL_fVar_wff"
  fun op tsubst_I0 _ = () val op tsubst_I0 = TDB.find "tsubst_I0"
  fun op tsubst_I _ = () val op tsubst_I = TDB.find "tsubst_I"
  fun op vl2sl_wfvl_MEM_var_no_bound _ = ()
  val op vl2sl_wfvl_MEM_var_no_bound = TDB.find
    "vl2sl_wfvl_MEM_var_no_bound"
  fun op wfabsap_vl2sl_MAP_Var' _ = ()
  val op wfabsap_vl2sl_MAP_Var' = TDB.find "wfabsap_vl2sl_MAP_Var'"
  fun op wfdpvl_ALL_DISTINCT_okvnames_wff _ = ()
  val op wfdpvl_ALL_DISTINCT_okvnames_wff = TDB.find
    "wfdpvl_ALL_DISTINCT_okvnames_wff"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "wff"

val wff_grammars = valOf (Parse.grammarDB {thyname = "wff"})
end
