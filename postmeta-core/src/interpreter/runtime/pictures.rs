use postmeta_graphics::types::Picture;

use crate::equation::VarId;
use crate::types::Value;
use crate::variables::{VarValue, Variables};

/// Runtime owner of picture output and `currentpicture` synchronization.
#[derive(Debug)]
pub(in crate::interpreter) struct PictureManager {
    output_pictures: Vec<Picture>,
    current_picture: Picture,
    currentpicture_dirty: bool,
}

impl PictureManager {
    pub(in crate::interpreter) const fn new() -> Self {
        Self {
            output_pictures: Vec::new(),
            current_picture: Picture::new(),
            currentpicture_dirty: false,
        }
    }

    pub(in crate::interpreter) fn output(&self) -> &[Picture] {
        &self.output_pictures
    }

    pub(in crate::interpreter) const fn current_picture(&self) -> &Picture {
        &self.current_picture
    }

    pub(in crate::interpreter) fn clone_current_picture(&self) -> Picture {
        self.current_picture.clone()
    }

    pub(in crate::interpreter) fn push_output(&mut self, picture: Picture) {
        self.output_pictures.push(picture);
    }

    pub(in crate::interpreter) const fn currentpicture_dirty(&self) -> bool {
        self.currentpicture_dirty
    }

    pub(in crate::interpreter) fn sync_currentpicture_variable(
        &mut self,
        variables: &mut Variables,
    ) {
        if !self.currentpicture_dirty {
            return;
        }
        self.currentpicture_dirty = false;
        if let Some(var_id) = variables.lookup_existing("currentpicture") {
            variables.set_known(var_id, Value::Picture(self.current_picture.clone()));
        }
    }

    pub(in crate::interpreter) fn with_target_picture<F>(
        &mut self,
        variables: &mut Variables,
        pic_name: &str,
        apply: F,
    ) where
        F: FnOnce(&mut Picture),
    {
        if pic_name == "currentpicture" {
            apply(&mut self.current_picture);
            self.currentpicture_dirty = true;
            return;
        }

        let mut target =
            variables
                .lookup_existing(pic_name)
                .map_or_else(Picture::default, |var_id| match variables.take(var_id) {
                    VarValue::Known(Value::Picture(p)) => p,
                    _ => Picture::default(),
                });

        apply(&mut target);

        let var_id = variables.lookup(pic_name);
        variables.set_known(var_id, Value::Picture(target));
    }

    pub(in crate::interpreter) fn sync_runtime_for_picture_assignment(
        &mut self,
        variables: &Variables,
        assigned_var: VarId,
        value: &Value,
    ) {
        if let Value::Picture(picture) = value
            && variables
                .lookup_existing("currentpicture")
                .is_some_and(|currentpicture_var| currentpicture_var == assigned_var)
        {
            self.current_picture = picture.clone();
        }
    }
}
