structure fVinstTheory :> fVinstTheory =
struct
  
  val _ = if !Globals.print_thy_loads
    then TextIO.print "Loading fVinstTheory ... "
    else ()
  
  open Type Term Thm
  local open fsytxTheory in end;
  
  structure TDB = struct
    val thydata = 
      TheoryReader.load_thydata "fVinst"
        (holpathdb.subst_pathvars "/Users/yimingxu/Documents/GitHub/DSTPMFcopy/formalisation/fVinstTheory.dat")
    fun find s = Redblackmap.find (thydata,s)
  end
  
  fun op shift_bmap'_def _ = ()
  val op shift_bmap'_def = TDB.find "shift_bmap'_def"
  fun op bmap_eff_def _ = () val op bmap_eff_def = TDB.find "bmap_eff_def"
  fun op bmap_equiv_def _ = ()
  val op bmap_equiv_def = TDB.find "bmap_equiv_def"
  fun op fVmap_rename_def _ = ()
  val op fVmap_rename_def = TDB.find "fVmap_rename_def"
  fun op fVmap_eff_def _ = ()
  val op fVmap_eff_def = TDB.find "fVmap_eff_def"
  fun op slprpl_id _ = () val op slprpl_id = TDB.find "slprpl_id"
  fun op ok_abs_slprpl_fix _ = ()
  val op ok_abs_slprpl_fix = TDB.find "ok_abs_slprpl_fix"
  fun op tprpl_FMAP_MAP_tprpl _ = ()
  val op tprpl_FMAP_MAP_tprpl = TDB.find "tprpl_FMAP_MAP_tprpl"
  fun op FDOM_shift_bmap' _ = ()
  val op FDOM_shift_bmap' = TDB.find "FDOM_shift_bmap'"
  fun op FAPPLY_shift_bmap' _ = ()
  val op FAPPLY_shift_bmap' = TDB.find "FAPPLY_shift_bmap'"
  fun op tprpl_shift_bmap_shift_bmap' _ = ()
  val op tprpl_shift_bmap_shift_bmap' = TDB.find
    "tprpl_shift_bmap_shift_bmap'"
  fun op tprpl_shift_bmap'_tshift _ = ()
  val op tprpl_shift_bmap'_tshift = TDB.find "tprpl_shift_bmap'_tshift"
  fun op shift_bmap'_FMAP_MAP _ = ()
  val op shift_bmap'_FMAP_MAP = TDB.find "shift_bmap'_FMAP_MAP"
  fun op shift_bmap_shift_bmap'_bmap_eff _ = ()
  val op shift_bmap_shift_bmap'_bmap_eff = TDB.find
    "shift_bmap_shift_bmap'_bmap_eff"
  fun op bmap_eff_tprpl _ = ()
  val op bmap_eff_tprpl = TDB.find "bmap_eff_tprpl"
  fun op bmap_eff_shift_bmap _ = ()
  val op bmap_eff_shift_bmap = TDB.find "bmap_eff_shift_bmap"
  fun op shift_bmap_equiv _ = ()
  val op shift_bmap_equiv = TDB.find "shift_bmap_equiv"
  fun op bmap_eff_slprpl _ = ()
  val op bmap_eff_slprpl = TDB.find "bmap_eff_slprpl"
  fun op bmap_eff_fprpl _ = ()
  val op bmap_eff_fprpl = TDB.find "bmap_eff_fprpl"
  fun op shift_bmap_shift_bmap'_equiv _ = ()
  val op shift_bmap_shift_bmap'_equiv = TDB.find
    "shift_bmap_shift_bmap'_equiv"
  fun op fprpl_FMAP_MAP _ = ()
  val op fprpl_FMAP_MAP = TDB.find "fprpl_FMAP_MAP"
  fun op fVinst_id _ = () val op fVinst_id = TDB.find "fVinst_id"
  fun op FDOM_fVmap_rename _ = ()
  val op FDOM_fVmap_rename = TDB.find "FDOM_fVmap_rename"
  fun op FAPPLY_fVmap_rename _ = ()
  val op FAPPLY_fVmap_rename = TDB.find "FAPPLY_fVmap_rename"
  fun op fVinst_fabs _ = () val op fVinst_fabs = TDB.find "fVinst_fabs"
  fun op ok_abs_slprpl _ = ()
  val op ok_abs_slprpl = TDB.find "ok_abs_slprpl"
  fun op fVar_prpl_eq_lemma _ = ()
  val op fVar_prpl_eq_lemma = TDB.find "fVar_prpl_eq_lemma"
  fun op fVar_prpl_fabs1 _ = ()
  val op fVar_prpl_fabs1 = TDB.find "fVar_prpl_fabs1"
  fun op ofFMAP_EMPTY _ = () val op ofFMAP_EMPTY = TDB.find "ofFMAP_EMPTY"
  fun op ofFMAP_UNION _ = () val op ofFMAP_UNION = TDB.find "ofFMAP_UNION"
  fun op ofFMAP_Sing _ = () val op ofFMAP_Sing = TDB.find "ofFMAP_Sing"
  fun op ofFMAP_FDOM _ = () val op ofFMAP_FDOM = TDB.find "ofFMAP_FDOM"
  fun op ofFMAP_Sing_EMPTY _ = ()
  val op ofFMAP_Sing_EMPTY = TDB.find "ofFMAP_Sing_EMPTY"
  fun op ffv_fVinst _ = () val op ffv_fVinst = TDB.find "ffv_fVinst"
  fun op sbounds_frename_EMPTY _ = ()
  val op sbounds_frename_EMPTY = TDB.find "sbounds_frename_EMPTY"
  fun op fVars_fabs _ = () val op fVars_fabs = TDB.find "fVars_fabs"
  fun op fVmap_no_bound_lemma _ = ()
  val op fVmap_no_bound_lemma = TDB.find "fVmap_no_bound_lemma"
  fun op wffVmap_fVmap_rename _ = ()
  val op wffVmap_fVmap_rename = TDB.find "wffVmap_fVmap_rename"
  fun op wffVmap_no_vbound _ = ()
  val op wffVmap_no_vbound = TDB.find "wffVmap_no_vbound"
  fun op fVars_DRESTRICT_fVinst_eq _ = ()
  val op fVars_DRESTRICT_fVinst_eq = TDB.find "fVars_DRESTRICT_fVinst_eq"
  fun op fVars_fprpl _ = () val op fVars_fprpl = TDB.find "fVars_fprpl"
  fun op fVars_fVinst _ = () val op fVars_fVinst = TDB.find "fVars_fVinst"
  fun op fVinst_EQ _ = () val op fVinst_EQ = TDB.find "fVinst_EQ"
  fun op wff_fVinst _ = () val op wff_fVinst = TDB.find "wff_fVinst"
  
  
val _ = if !Globals.print_thy_loads then TextIO.print "done\n" else ()
val _ = Theory.load_complete "fVinst"

val fVinst_grammars = valOf (Parse.grammarDB {thyname = "fVinst"})
end
