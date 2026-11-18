import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block135_checked : centerBlock 135 = true := by decide +kernel
#print axioms block135_checked
end PythiaCert.Output
