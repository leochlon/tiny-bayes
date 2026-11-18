import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block4_checked : centerBlock 4 = true := by decide +kernel
#print axioms block4_checked
end PythiaCert.Output
