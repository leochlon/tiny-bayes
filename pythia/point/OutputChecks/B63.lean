import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block63_checked : centerBlock 63 = true := by decide +kernel
#print axioms block63_checked
end PythiaCert.Output
