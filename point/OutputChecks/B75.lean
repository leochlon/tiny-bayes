import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block75_checked : centerBlock 75 = true := by decide +kernel
#print axioms block75_checked
end PythiaCert.Output
