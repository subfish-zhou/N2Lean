prelude
import init.data.nat.basic init.data.string.basic

def lean.version : nat × nat × nat :=
(3, 40, 0)

def lean.githash : string :=
"82216a493580a309a04b02c2b6eb5f82f0aef192"

def lean.is_release : bool :=
1 ≠ 0

/-- Additional version description like "nightly-2018-03-11" -/
def lean.special_version_desc : string :=
""
