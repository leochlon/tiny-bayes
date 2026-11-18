import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block156_checked : centerBlock 156 = true := by decide +kernel
#print axioms block156_checked
end PythiaCert.Output
