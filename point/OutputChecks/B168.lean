import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block168_checked : centerBlock 168 = true := by decide +kernel
#print axioms block168_checked
end PythiaCert.Output
