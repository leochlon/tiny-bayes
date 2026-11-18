import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block150_checked : centerBlock 150 = true := by decide +kernel
#print axioms block150_checked
end PythiaCert.Output
