import Streaming
import qualified Streaming.Prelude as S
import Streaming.Extensible


aa = do
  yield_ ()
  yield_ "July"
  yield_ ()
  yield_ "August"
  yield_ ()
  yield_ "September"
  yield_ ()
  yield_ "October"