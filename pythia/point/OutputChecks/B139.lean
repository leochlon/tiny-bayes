import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block139_checked : centerBlock 139 = true := by decide +kernel
#print axioms block139_checked
end PythiaCert.Output
