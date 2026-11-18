import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block31_checked : centerBlock 31 = true := by decide +kernel
#print axioms block31_checked
end PythiaCert.Output
