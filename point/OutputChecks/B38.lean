import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block38_checked : centerBlock 38 = true := by decide +kernel
#print axioms block38_checked
end PythiaCert.Output
