import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block78_checked : centerBlock 78 = true := by decide +kernel
#print axioms block78_checked
end PythiaCert.Output
