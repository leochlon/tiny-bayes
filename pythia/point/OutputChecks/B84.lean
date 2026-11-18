import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block84_checked : centerBlock 84 = true := by decide +kernel
#print axioms block84_checked
end PythiaCert.Output
