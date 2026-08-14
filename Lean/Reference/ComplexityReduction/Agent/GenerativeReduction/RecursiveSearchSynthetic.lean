/- Copyright (c) 2026. -/

import ComplexityReduction.Agent.GenerativeReduction.RuleApplication

/-! Small domain-neutral fixtures for recursive frame and dependency tests. -/

namespace ComplexityReduction.Agent.GenerativeReduction.RecursiveSearchSynthetic

abbrev Source : Type := Bool

def sourceTrue : Source := true
def sourceFalse : Source := false

def First (source : Source) : Prop := source = true
def Second (source : Source) : Prop := source || false = true

theorem firstTrue : First sourceTrue := rfl
theorem secondTrue : Second sourceTrue := rfl

theorem dependentRule
    (source : Source)
    (_first : First source)
    (_second : Second source) : True :=
  True.intro

theorem twoLevelRule (proof : True) : True := proof

theorem selfLoop (proof : True) : True := proof

end ComplexityReduction.Agent.GenerativeReduction.RecursiveSearchSynthetic
