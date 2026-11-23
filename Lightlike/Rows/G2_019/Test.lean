import Lightlike.Rows.G2_019.WKBForms

/-! Smoke tests for row G2-019 (Airy functions, Hartle–Hawking / Vilenkin). -/

open Lightlike.Airy

#check @airy_wronskian
#check @hhWave_current
#check @vilenkinWave_current
#check @wkbDeriv_hasDerivAt
#check @wkb_wronskian
#check @wkb_relative_residual_tendsto
#check @vilenkinWKB_current
#check @vilenkinWKBDeriv_hasDerivAt

#print axioms vilenkinWKB_current
#print axioms airy_wronskian
