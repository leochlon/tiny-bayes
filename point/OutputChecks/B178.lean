import OutputDefs
namespace PythiaCert.Output
set_option maxRecDepth 100000
set_option maxHeartbeats 0
theorem block178_checked : centerBlock 178 = true := by decide +kernel
#print axioms block178_checked
end PythiaCert.Output
