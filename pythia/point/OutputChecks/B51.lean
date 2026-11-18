import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block51_checked : centerBlock 51 = true := by decide +kernel
#print axioms block51_checked
end PythiaCert.Output
