class Adapter(object):
  def __init__(self, value):
    self.is_array = self.is_object = self.is_string = self.is_int = self.is_float = self.is_null = False

    if value is None:
      self.is_null = True
    elif isinstance(value, list):
      self.is_array = True
    elif isinstance(value, dict):
      self.is_object = True
    elif isinstance(value, unicode):
      self.is_string = True
    elif isinstance(value, int) or isinstance(value, long):
      self.is_int = True
    elif isinstance(value, float):
      self.is_float = True
    else:
      raise TypeError("Unrecognized value: %s" % value)
    self.value = value

  def value_array(self):
    if self.is_array:
      return [adapt(x) for x in self.value]
    raise TypeError

  def value_object(self):
    if self.is_object:
      return {k: adapt(v) for k, v in self.value.items()}
    raise TypeError

  def value_string(self):
    if self.is_string:
      return self.value
    raise TypeError

  def value_int(self):
    if self.is_int:
      return self.value
    raise TypeError

  def value_float(self):
    if self.is_float:
      return self.value
    raise TypeError

  def tostring(self):
    return json.dumps(self.value)

# Given a value produced by Python's json module, returns a version
# that is compatible with some of the interface in Pycket's JsonBase
# from the pycket_json module.
def adapt(json):
  return Adapter(json)
