import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block146_checked : centerBlock 146 = true := by decide +kernel
#print axioms block146_checked
end PythiaCert.Output
