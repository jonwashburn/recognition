import Mathlib
import URC.Minimal

namespace IndisputableMonolith
namespace URCAdapters

/-- Route A adapter: treat a minimal URC bridge as the B (short lawful bridge)
    input for absolute-layer assembly. -/
@[simp] def RouteA_LawfulBridge : URCMinimal.LawfulBridge := URCMinimal.bridge

end URCAdapters
end IndisputableMonolith


