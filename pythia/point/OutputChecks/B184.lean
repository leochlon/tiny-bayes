import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block184_checked : centerBlock 184 = true := by decide +kernel
#print axioms block184_checked
end PythiaCert.Output
