import SetTheory.ZFC
import SetTheory.Relations
import SetTheory.Omega
import SetTheory.Recursive

namespace SetTheory
namespace Omega

open Classical

noncomputable def nat_succ := map_constructor ω set_succ
noncomputable def addn (n: Set) := recursive_map_constructor ω n nat_succ
noncomputable def add := map_constructor (ω × ω) (λ t => addn (pair_right t) ⸨(pair_left t)⸩)
infixl:112 "+" => operation_eval add

noncomputable def timesn (n: Set) := recursive_map_constructor ω ∅ (addn n)
noncomputable def times := map_constructor (ω × ω) (λ t => timesn (pair_right t) ⸨(pair_left t)⸩)
infixl:113 "*" => operation_eval times

end Omega
end SetTheory
