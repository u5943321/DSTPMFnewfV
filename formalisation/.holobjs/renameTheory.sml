structure renameTheory :> renameTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading renameTheory ... "
    else ()
  
  open Type Term Thm
  local open fsytxTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "rename"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMF/formalisation/renameTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op rnmap_def _ = () val op rnmap_def = TDB.find "rnmap_def"
  fun op gcont_def _ = () val op gcont_def = TDB.find "gcont_def"
  fun op trename_alt _ = () val op trename_alt = TDB.find "trename_alt"
  fun op FDOM_rnmap _ = () val op FDOM_rnmap = TDB.find "FDOM_rnmap"
  fun op FAPPLY_rnmap _ = () val op FAPPLY_rnmap = TDB.find "FAPPLY_rnmap"
  fun op trename_tinst _ = ()
  val op trename_tinst = TDB.find "trename_tinst"
  fun op no_subrename _ = () val op no_subrename = TDB.find "no_subrename"
  fun op cstt_rnmap _ = () val op cstt_rnmap = TDB.find "cstt_rnmap"
  fun op BIGUNION_is_cont _ = ()
  val op BIGUNION_is_cont = TDB.find "BIGUNION_is_cont"
  fun op trename_tinst_tfv _ = ()
  val op trename_tinst_tfv = TDB.find "trename_tinst_tfv"
  fun op FAPPLY_rnmap_SUBSET _ = ()
  val op FAPPLY_rnmap_SUBSET = TDB.find "FAPPLY_rnmap_SUBSET"
  fun op wfcod_rnmap_SUBSET _ = ()
  val op wfcod_rnmap_SUBSET = TDB.find "wfcod_rnmap_SUBSET"
  fun op wfcod_rnmap_BIGUNION _ = ()
  val op wfcod_rnmap_BIGUNION = TDB.find "wfcod_rnmap_BIGUNION"
  fun op FINITE_lemma _ = () val op FINITE_lemma = TDB.find "FINITE_lemma"
  fun op wft_trename0 _ = () val op wft_trename0 = TDB.find "wft_trename0"
  fun op frename_alt _ = () val op frename_alt = TDB.find "frename_alt"
  fun op frename_finst _ = ()
  val op frename_finst = TDB.find "frename_finst"
  fun op frename_finst_ffv _ = ()
  val op frename_finst_ffv = TDB.find "frename_finst_ffv"
  fun op gcont_is_cont _ = ()
  val op gcont_is_cont = TDB.find "gcont_is_cont"
  fun op gcont_of_cont _ = ()
  val op gcont_of_cont = TDB.find "gcont_of_cont"
  fun op gcont_FINITE _ = () val op gcont_FINITE = TDB.find "gcont_FINITE"
  fun op gcont_EMPTY _ = () val op gcont_EMPTY = TDB.find "gcont_EMPTY"
  fun op gcont_UNION _ = () val op gcont_UNION = TDB.find "gcont_UNION"
  fun op gcont_SING _ = () val op gcont_SING = TDB.find "gcont_SING"
  fun op wfcod_rnmap_tfv _ = ()
  val op wfcod_rnmap_tfv = TDB.find "wfcod_rnmap_tfv"
  fun op wft_trename _ = () val op wft_trename = TDB.find "wft_trename"
  fun op wfcod_rnmap_gcont _ = ()
  val op wfcod_rnmap_gcont = TDB.find "wfcod_rnmap_gcont"
  fun op wfcod_rnmap_cont _ = ()
  val op wfcod_rnmap_cont = TDB.find "wfcod_rnmap_cont"
  fun op wfcod_rnmap_ffv _ = ()
  val op wfcod_rnmap_ffv = TDB.find "wfcod_rnmap_ffv"
  fun op FINITE_BIGUNION_tfv _ = ()
  val op FINITE_BIGUNION_tfv = TDB.find "FINITE_BIGUNION_tfv"
  fun op wff_frename _ = () val op wff_frename = TDB.find "wff_frename"
  fun op mk_FALL_rename_eq _ = ()
  val op mk_FALL_rename_eq = TDB.find "mk_FALL_rename_eq"
  fun op frename_fix _ = () val op frename_fix = TDB.find "frename_fix"
  fun op ffv_fabs_SUBSET _ = ()
  val op ffv_fabs_SUBSET = TDB.find "ffv_fabs_SUBSET"
  fun op IN_tfv_trename _ = ()
  val op IN_tfv_trename = TDB.find "IN_tfv_trename"
  fun op trename_back _ = () val op trename_back = TDB.find "trename_back"
  fun op tprpl_FMAP_MAP_tabs_IN _ = ()
  val op tprpl_FMAP_MAP_tabs_IN = TDB.find "tprpl_FMAP_MAP_tabs_IN"
  fun op slprpl_FMAP_MAP_abssl_IN _ = ()
  val op slprpl_FMAP_MAP_abssl_IN = TDB.find "slprpl_FMAP_MAP_abssl_IN"
  fun op fprpl_FMAP_MAP_fabs_IN _ = ()
  val op fprpl_FMAP_MAP_fabs_IN = TDB.find "fprpl_FMAP_MAP_fabs_IN"
  fun op fVar_subst_fabs _ = ()
  val op fVar_subst_fabs = TDB.find "fVar_subst_fabs"
  fun op NOTIN_trename _ = ()
  val op NOTIN_trename = TDB.find "NOTIN_trename"
  fun op NOTIN_frename _ = ()
  val op NOTIN_frename = TDB.find "NOTIN_frename"
  fun op frename_FALLL _ = ()
  val op frename_FALLL = TDB.find "frename_FALLL"
  fun op ffv_FALLL _ = () val op ffv_FALLL = TDB.find "ffv_FALLL"
  fun op BIGUNION_IMAGE_sbounds_tfv _ = ()
  val op BIGUNION_IMAGE_sbounds_tfv = TDB.find "BIGUNION_IMAGE_sbounds_tfv"
  fun op BIGUNION_IMAGE_sbounds_ffv _ = ()
  val op BIGUNION_IMAGE_sbounds_ffv = TDB.find "BIGUNION_IMAGE_sbounds_ffv"
  fun op fresh_name_ex _ = ()
  val op fresh_name_ex = TDB.find "fresh_name_ex"
  fun op wff_fVar_subst _ = ()
  val op wff_fVar_subst = TDB.find "wff_fVar_subst"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "rename"

val rename_grammars = valOf (Parse.grammarDB {thyname = "rename"})
end
