import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block163_checked : centerBlock 163 = true := by decide +kernel
#print axioms block163_checked
end PythiaCert.Output
