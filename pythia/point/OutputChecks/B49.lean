import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block49_checked : centerBlock 49 = true := by decide +kernel
#print axioms block49_checked
end PythiaCert.Output
