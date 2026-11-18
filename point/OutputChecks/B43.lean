import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block43_checked : centerBlock 43 = true := by decide +kernel
#print axioms block43_checked
end PythiaCert.Output
