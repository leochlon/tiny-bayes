import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block187_checked : centerBlock 187 = true := by decide +kernel
#print axioms block187_checked
end PythiaCert.Output
