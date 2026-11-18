import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block64_checked : centerBlock 64 = true := by decide +kernel
#print axioms block64_checked
end PythiaCert.Output
