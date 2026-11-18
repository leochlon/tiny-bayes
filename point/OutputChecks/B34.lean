import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block34_checked : centerBlock 34 = true := by decide +kernel
#print axioms block34_checked
end PythiaCert.Output
