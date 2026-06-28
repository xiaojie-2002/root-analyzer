#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
根图分析 - RootVision
版本: v1.0
"""
__version__ = "1.0"

import sys
import os
import json
import csv
import tkinter as tk
from tkinter import ttk, filedialog, messagebox, scrolledtext, simpledialog
from PIL import Image, ImageTk, ImageDraw, ImageFont
import threading
import queue
import time
from datetime import datetime
import traceback
import warnings
import colorsys
import itertools
import math
import numpy as np
import multiprocessing
from concurrent.futures import ProcessPoolExecutor, as_completed, TimeoutError
import gc
import psutil  # 添加内存监控


# 检查Python版本
def check_python_version():
    """检查Python版本兼容性"""
    python_version = sys.version_info

    if python_version < (3, 8):
        print(f"警告: 当前Python版本 {python_version.major}.{pytn_version.minor}")
        print("建议升级到Python 3.8或更高版本")

    return True


# 检查并导入必要的库
def check_dependencies():
    """检查并导入依赖库"""
    required_libs = [
        ('opencv-python', 'cv2'),
        ('numpy', 'numpy'),
        ('scikit-image', 'skimage'),
        ('scipy', 'scipy'),
        ('matplotlib', 'matplotlib'),
        ('Pillow', 'PIL'),
        ('psutil', 'psutil')  # 添加psutil用于内存监控
    ]

    missing_libs = []
    imported_modules = []

    for pip_name, import_name in required_libs:
        try:
            if import_name == 'cv2':
                import cv2
                globals()['cv2'] = cv2
                imported_modules.append(('cv2', cv2))
            elif import_name == 'numpy':
                import numpy as np
                globals()['np'] = np
                imported_modules.append(('numpy', np))
            elif import_name == 'skimage':
                import skimage
                from skimage import morphology, measure, segmentation, filters, color, draw
                globals()['skimage'] = skimage
                globals()['morphology'] = morphology
                globals()['measure'] = measure
                globals()['segmentation'] = segmentation
                globals()['filters'] = filters
                globals()['color'] = color
                globals()['draw'] = draw
                imported_modules.append(('skimage', skimage))
            elif import_name == 'scipy':
                from scipy import ndimage, spatial
                globals()['ndimage'] = ndimage
                globals()['spatial'] = spatial
                imported_modules.append(('scipy', ndimage))
            elif import_name == 'matplotlib':
                import matplotlib
                matplotlib.use('Agg')  # 使用非GUI后端
                import matplotlib.pyplot as plt
                import matplotlib.patches as patches
                from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
                globals()['plt'] = plt
                globals()['patches'] = patches
                globals()['FigureCanvasTkAgg'] = FigureCanvasTkAgg
                imported_modules.append(('matplotlib', matplotlib))
            elif import_name == 'PIL':
                # PIL已经导入，这里只是确认
                imported_modules.append(('PIL', 'Image/ImageTk'))
            elif import_name == 'psutil':
                import psutil
                globals()['psutil'] = psutil
                imported_modules.append(('psutil', psutil))
        except ImportError as e:
            missing_libs.append(pip_name)
            print(f"导入{import_name}失败: {e}")
        except Exception as e:
            print(f"导入{import_name}时发生其他错误: {e}")
            missing_libs.append(pip_name)

    # 设置警告过滤
    warnings.filterwarnings('ignore', category=UserWarning)
    warnings.filterwarnings('ignore', category=FutureWarning)
    warnings.filterwarnings('ignore', category=DeprecationWarning)

    return missing_libs, imported_modules


# 检查和修复兼容性问题
check_python_version()
missing_libs, imported_modules = check_dependencies()

if missing_libs:
    print(f"缺少必要的库: {', '.join(missing_libs)}")
    print("请运行: pip install " + " ".join(missing_libs))

    # 创建简单的错误窗口
    try:
        error_root = tk.Tk()
        error_root.withdraw()
        messagebox.showerror(
            "缺少依赖库",
            f"缺少以下必要的Python库:\n\n{', '.join(missing_libs)}\n\n"
            f"请运行安装脚本:\n\n"
            f"pip install {' '.join(missing_libs)}"
        )
        error_root.destroy()
    except:
        pass
    sys.exit(1)
else:
    print("所有依赖库已成功导入:")


class RootSystemAnalyzer:
    """根系分析器核心类"""

    # 默认根系直径分级标准 (name, min_mm, max_mm)
    DEFAULT_DIAMETER_CLASSES = [
        ('超细根', 0.0, 0.5),
        ('细根',   0.5, 1.0),
        ('中根',   1.0, 2.0),
        ('粗根',   2.0, 5.0),
        ('超粗根', 5.0, float('inf')),
    ]

    def __init__(self, pixel_to_mm=0.1):
        self.pixel_to_mm = pixel_to_mm
        self.results = {}
        self.analysis_history = []
        self.scale_bar_length_mm = 10  # 默认比例尺长度(mm)
        self.scale_bar_position = (50, 50)  # 比例尺位置

        # 简化：只保存计数相关数据
        self.root_count = 0
        self.connected_components = []  # 连通组件信息

        # 添加根系参数
        self.root_parameters = {
            'total_length': 0.0,  # 总根长(mm)
            'total_area': 0.0,  # 总根系面积(mm²)
            'total_volume': 0.0,  # 总根体积(mm³)
            'total_surface': 0.0,  # 总根表面积(mm²)
            'specific_root_length': 0.0,  # 比根长(mm/mm²)
            'avg_diameter': 0.0,  # 平均根直径(mm)
            'diameter_distribution': {}  # 直径分布
        }

        # 过滤统计信息
        self.filter_stats = {
            'total_regions': 0,
            'filtered_regions': 0,
            'removed_regions': 0,
            'removal_percentage': 0.0
        }

        # 扫描图像专用参数
        self.scan_params = {
            'is_scanned': False,  # 是否为扫描图像
            'background_type': 'light',  # 背景类型：light/dark
            'scan_quality': 'high',  # 扫描质量：high/medium/low
            'resolution_dpi': 300,  # 扫描分辨率
        }

        # 扫描图像优化标志
        self.use_scan_optimization = False

        # 图像增强方法
        self.enhance_method = 'adaptive'  # 默认自适应增强

        # 扫描图像增强标志
        self.scan_enhanced = None

        # ROI区域（图像坐标），None表示全图分析
        self.roi_active = None

        # 自定义直径分级，None=使用DEFAULT_DIAMETER_CLASSES
        self.diameter_classes = None

    def _get_diameter_classes(self):
        """返回有效直径分级列表 [(name, min_mm, max_mm), ...]"""
        if self.diameter_classes and len(self.diameter_classes) >= 2:
            return self.diameter_classes
        return list(self.DEFAULT_DIAMETER_CLASSES)

    def _get_class_suffix_keys(self, class_name):
        """为给定分级名生成 results dict 键名"""
        return {
            'count': f'{class_name}数量',
            'volume': f'{class_name}体积(mm³)',
            'volume_pct': f'{class_name}体积占比(%)',
            'avg_diam': f'{class_name}平均直径(mm)',
        }

    def load_image(self, image_path):
        """加载图像"""
        try:
            self.original_image = cv2.imread(image_path)
            if self.original_image is None:
                raise ValueError(f"无法读取图像: {image_path}")

            self.image_path = image_path
            self.image_name = os.path.basename(image_path)

            # 获取图像尺寸
            self.image_height, self.image_width = self.original_image.shape[:2]

            # 创建原始图像的副本用于绘图
            self.display_image = self.original_image.copy()

            # 转换为灰度图
            self.gray_image = cv2.cvtColor(self.original_image, cv2.COLOR_BGR2GRAY)

            # 检测扫描图像特征
            self._detect_scan_image_characteristics()

            # 根据检测结果选择增强方法
            if self.use_scan_optimization:
                # 使用扫描图像增强
                self.enhanced_image = self._enhance_scanned_image(self.gray_image)
                self.scan_enhanced = self.enhanced_image.copy()
            else:
                # 使用原有增强方法
                clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
                self.enhanced_image = clahe.apply(self.gray_image)

            return True, "图像加载成功"
        except Exception as e:
            return False, f"图像加载失败: {str(e)}"

    def _detect_scan_image_characteristics(self):
        """检测扫描图像特征"""
        try:
            # 计算图像统计特征
            mean_val = np.mean(self.gray_image)
            std_val = np.std(self.gray_image)

            # 计算边缘检测
            edges = cv2.Canny(self.gray_image, 50, 150)
            edge_percentage = np.sum(edges > 0) / (self.gray_image.shape[0] * self.gray_image.shape[1])

            # 计算直方图
            hist = cv2.calcHist([self.gray_image], [0], None, [256], [0, 256])
            hist_peaks = self._check_histogram_peaks(hist)

            # 判断是否为扫描图像
            # 扫描图像通常背景均匀（标准差小），边缘占比低，直方图有明显峰
            is_uniform_background = std_val < 30
            has_low_edge_percentage = edge_percentage < 0.1
            has_clear_peaks = hist_peaks

            if is_uniform_background and has_low_edge_percentage:
                self.scan_params['is_scanned'] = True

                # 检测背景类型（亮/暗）
                self.scan_params['background_type'] = 'light' if mean_val > 128 else 'dark'

                # 估计扫描质量
                hist_smoothness = np.std(hist)
                if hist_smoothness < 100:
                    self.scan_params['scan_quality'] = 'high'
                elif hist_smoothness < 300:
                    self.scan_params['scan_quality'] = 'medium'
                else:
                    self.scan_params['scan_quality'] = 'low'

                print(
                    f"检测到扫描图像: 背景类型={self.scan_params['background_type']}, 质量={self.scan_params['scan_quality']}")

        except Exception as e:
            print(f"扫描图像检测失败: {e}")
            self.scan_params['is_scanned'] = False

    def _check_histogram_peaks(self, hist):
        """检查直方图是否有明显峰"""
        try:
            # 寻找峰值
            hist_flat = hist.flatten()

            # 计算平滑后的直方图
            hist_smooth = np.convolve(hist_flat, np.ones(5) / 5, mode='same')

            # 寻找局部极大值
            peaks = []
            for i in range(1, len(hist_smooth) - 1):
                if hist_smooth[i] > hist_smooth[i - 1] and hist_smooth[i] > hist_smooth[i + 1]:
                    peaks.append(i)

            # 如果有2个或更少的明显峰（黑白图像），可能是扫描图像
            return len(peaks) <= 2
        except:
            return False

    def _enhance_scanned_image(self, gray_image):
        """
        针对扫描图像的简化增强
        扫描图像通常背景均匀，无需复杂的光照校正
        """
        # 轻微对比度增强，避免过度处理
        return self._mild_contrast_enhance(gray_image)

    def _mild_contrast_enhance(self, image):
        """轻微对比度增强，避免过度处理"""
        # 1. 获取图像的最小和最大像素值
        min_val = np.min(image)
        max_val = np.max(image)

        # 2. 线性拉伸到[0, 255]
        if max_val > min_val:
            enhanced = ((image - min_val) * 255.0 / (max_val - min_val)).astype(np.uint8)
        else:
            enhanced = image

        # 3. 轻微锐化（可选，根据扫描质量决定）
        if self.scan_params['scan_quality'] == 'high':
            kernel = np.array([[0, -1, 0],
                               [-1, 5, -1],
                               [0, -1, 0]])
            enhanced = cv2.filter2D(enhanced, -1, kernel)

        return enhanced

    def enable_scan_optimization(self, enable=True):
        """启用或禁用扫描图像优化"""
        self.use_scan_optimization = enable
        if enable and hasattr(self, 'gray_image'):
            # 重新增强图像
            self.enhanced_image = self._enhance_scanned_image(self.gray_image)
            self.scan_enhanced = self.enhanced_image.copy()
        elif hasattr(self, 'gray_image'):
            # 恢复原有增强方法
            clahe = cv2.createCLAHE(clipLimit=2.0, tileGridSize=(8, 8))
            self.enhanced_image = clahe.apply(self.gray_image)

        return self.use_scan_optimization

    def set_scan_background_type(self, bg_type):
        """设置扫描背景类型"""
        if bg_type in ['light', 'dark', 'auto']:
            self.scan_params['background_type'] = bg_type
            if bg_type == 'auto':
                # 自动检测
                mean_val = np.mean(self.gray_image) if hasattr(self, 'gray_image') else 128
                self.scan_params['background_type'] = 'light' if mean_val > 128 else 'dark'
            return True
        return False

    def set_scan_quality(self, quality):
        """设置扫描质量"""
        if quality in ['high', 'medium', 'low', 'auto']:
            self.scan_params['scan_quality'] = quality
            return True
        return False

    def segment_roots(self, method='otsu'):
        """分割根系 - 保留大津法，增加扫描图像优化"""
        try:
            # 如果启用扫描图像优化，使用专用分割方法
            if self.use_scan_optimization and self.scan_params['is_scanned']:
                return self._segment_scanned_roots()

            # 否则使用原大津法
            _, binary = cv2.threshold(
                self.enhanced_image, 0, 255,
                cv2.THRESH_BINARY_INV + cv2.THRESH_OTSU
            )

            # 基本形态学操作
            kernel = np.ones((3, 3), np.uint8)
            binary = cv2.morphologyEx(binary, cv2.MORPH_OPEN, kernel)
            binary = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel)

            self.binary_mask = binary

            # 应用ROI裁剪
            if self.roi_active is not None:
                x1, y1, x2, y2 = [int(v) for v in self.roi_active]
                h, w = self.binary_mask.shape[:2]
                x1, x2 = max(0, x1), min(w, x2)
                y1, y2 = max(0, y1), min(h, y2)
                roi_mask = np.zeros((h, w), dtype=np.uint8)
                roi_mask[y1:y2, x1:x2] = 255
                self.binary_mask = cv2.bitwise_and(self.binary_mask, roi_mask)

            return True, "图像分割完成（使用大津法）"
        except Exception as e:
            return False, f"分割失败: {str(e)}"

    def _segment_scanned_roots(self):
        """针对扫描图像优化的分割方法"""
        try:
            # 扫描图像通常对比度好，使用简单的阈值分割
            # 计算自适应阈值
            mean_val = np.mean(self.enhanced_image)

            if self.scan_params['background_type'] == 'light':
                # 对于白色背景，根系通常较暗
                _, binary = cv2.threshold(
                    self.enhanced_image,
                    mean_val * 0.6,  # 自适应阈值
                    255,
                    cv2.THRESH_BINARY_INV
                )
            else:  # 暗背景
                # 对于黑色背景，根系通常较亮
                _, binary = cv2.threshold(
                    self.enhanced_image,
                    mean_val * 1.4,  # 自适应阈值
                    255,
                    cv2.THRESH_BINARY
                )

            # 简化形态学操作（扫描图像通常干净）
            kernel = np.ones((2, 2), np.uint8)
            binary = cv2.morphologyEx(binary, cv2.MORPH_CLOSE, kernel, iterations=1)
            binary = cv2.morphologyEx(binary, cv2.MORPH_OPEN, kernel, iterations=1)

            self.binary_mask = binary

            # 应用ROI裁剪
            if self.roi_active is not None:
                x1, y1, x2, y2 = [int(v) for v in self.roi_active]
                h, w = self.binary_mask.shape[:2]
                x1, x2 = max(0, x1), min(w, x2)
                y1, y2 = max(0, y1), min(h, y2)
                roi_mask = np.zeros((h, w), dtype=np.uint8)
                roi_mask[y1:y2, x1:x2] = 255
                self.binary_mask = cv2.bitwise_and(self.binary_mask, roi_mask)

            return True, "扫描图像分割完成"

        except Exception as e:
            # 如果失败，回退到原方法
            return False, f"扫描图像分割失败: {str(e)}"

    def filter_non_roots(self, min_length=5, min_area=20, min_aspect_ratio=1.0):
        """
        简化版根系过滤算法 - 只保留三个关键参数
        增加扫描图像优化版本
        """
        try:
            # 如果启用扫描图像优化，使用专用过滤方法
            if self.use_scan_optimization and self.scan_params['is_scanned']:
                return self._filter_non_roots_scanned(min_length, min_area, min_aspect_ratio)

            # 原有过滤算法
            labeled_image = measure.label(self.binary_mask)
            props = measure.regionprops_table(
                labeled_image,
                properties=[
                    'label', 'area', 'major_axis_length', 'minor_axis_length'
                ]
            )

            n_regions = len(props['label'])
            filtered_mask = np.zeros_like(self.binary_mask)
            filtered_count = 0

            # 预计算条件
            major_axis = props['major_axis_length']
            minor_axis = props['minor_axis_length']
            areas = props['area']

            # 避免除零
            minor_axis_safe = np.where(minor_axis == 0, 0.01, minor_axis)
            aspect_ratios = major_axis / minor_axis_safe

            # 1. 面积过滤
            area_condition = areas >= min_area

            # 2. 长度过滤
            length_condition = major_axis >= min_length

            # 3. 纵横比过滤
            aspect_condition = aspect_ratios >= min_aspect_ratio

            # 综合所有条件
            valid_conditions = area_condition & length_condition & aspect_condition
            valid_indices = np.where(valid_conditions)[0]

            # 应用过滤结果
            for idx in valid_indices:
                label = props['label'][idx]
                filtered_mask[labeled_image == label] = 255
                filtered_count += 1

            # 后处理 - 形态学操作连接断裂的根系
            if filtered_count > 0:
                kernel = np.ones((3, 3), np.uint8)
                # 先闭运算填充小孔
                filtered_mask = cv2.morphologyEx(filtered_mask, cv2.MORPH_CLOSE, kernel, iterations=1)
                # 再开运算去除小噪点
                filtered_mask = cv2.morphologyEx(filtered_mask, cv2.MORPH_OPEN, kernel, iterations=1)

            self.filtered_mask = filtered_mask
            self.filtered_count = filtered_count

            # 保存过滤统计信息
            self.filter_stats = {
                'total_regions': n_regions,
                'filtered_regions': filtered_count,
                'removed_regions': n_regions - filtered_count,
                'removal_percentage': ((n_regions - filtered_count) / n_regions * 100) if n_regions > 0 else 0,
                'average_area': np.mean(areas) if len(areas) > 0 else 0,
                'average_aspect_ratio': np.mean(aspect_ratios) if len(aspect_ratios) > 0 else 0
            }

            # 保存被过滤区域的统计信息
            filtered_areas = areas[valid_indices] if len(valid_indices) > 0 else []
            if len(filtered_areas) > 0:
                self.filter_stats.update({
                    'filtered_min_area': np.min(filtered_areas),
                    'filtered_max_area': np.max(filtered_areas),
                    'filtered_avg_area': np.mean(filtered_areas)
                })

            return True, f"过滤完成，保留{filtered_count}个根系对象（过滤掉{n_regions - filtered_count}个）"
        except Exception as e:
            # 如果过滤失败，使用原始掩码
            self.filtered_mask = self.binary_mask.copy()
            labeled = measure.label(self.binary_mask)
            self.filtered_count = np.max(labeled) if np.max(labeled) > 0 else 0
            self.filter_stats = {
                'total_regions': self.filtered_count,
                'filtered_regions': self.filtered_count,
                'removed_regions': 0,
                'removal_percentage': 0.0,
                'error': str(e)
            }
            return False, f"过滤失败，使用原始图像: {str(e)}"

    def _filter_non_roots_scanned(self, min_length=3, min_area=10, min_aspect_ratio=0.8):
        """
        针对扫描图像的过滤优化
        扫描图像中的根系通常更清晰，噪声更少
        """
        try:
            labeled_image = measure.label(self.binary_mask)
            props = measure.regionprops_table(
                labeled_image,
                properties=['label', 'area', 'major_axis_length', 'minor_axis_length']
            )

            n_regions = len(props['label'])
            filtered_mask = np.zeros_like(self.binary_mask)
            filtered_count = 0

            # 扫描图像可以放宽过滤条件
            # 因为根系通常更完整，噪声更少
            for i in range(n_regions):
                area = props['area'][i]
                major_axis = props['major_axis_length'][i]
                minor_axis = props['minor_axis_length'][i]

                # 避免除零
                if minor_axis == 0:
                    aspect_ratio = 0
                else:
                    aspect_ratio = major_axis / minor_axis

                # 扫描图像的过滤条件（更宽松）
                if (area >= min_area and
                        major_axis >= min_length and
                        aspect_ratio >= min_aspect_ratio):
                    label = props['label'][i]
                    filtered_mask[labeled_image == label] = 255
                    filtered_count += 1

            self.filtered_mask = filtered_mask
            self.filtered_count = filtered_count

            # 保存过滤统计
            self.filter_stats = {
                'total_regions': n_regions,
                'filtered_regions': filtered_count,
                'removed_regions': n_regions - filtered_count,
                'removal_percentage': ((n_regions - filtered_count) / n_regions * 100) if n_regions > 0 else 0,
                'average_area': np.mean(props['area']) if len(props['area']) > 0 else 0,
                'scan_optimized': True  # 标记为扫描优化
            }

            return True, f"扫描图像过滤完成，保留{filtered_count}个根系对象"

        except Exception as e:
            # 如果失败，使用原过滤方法
            return self.filter_non_roots(min_length, min_area, min_aspect_ratio)

    def count_roots(self, min_size=50):
        """简化版：只计数根系，不分离个体细节"""
        try:
            if not hasattr(self, 'filtered_mask') or np.sum(self.filtered_mask) == 0:
                self.root_count = 0
                return True, "没有检测到根系"

            # 使用连通域分析计算根系数量
            num_labels, labels, stats, centroids = cv2.connectedComponentsWithStats(
                self.filtered_mask, connectivity=8
            )

            # 统计满足最小尺寸条件的根系
            root_count = 0
            self.connected_components = []

            for i in range(1, num_labels):  # 跳过背景(0)
                area = stats[i, cv2.CC_STAT_AREA]
                if area >= min_size:
                    root_count += 1

                    # 计算根系长度（使用骨架长度）
                    root_mask = (labels == i).astype(np.uint8) * 255
                    root_length = self._calculate_root_length(root_mask)

                    # 计算根系直径
                    root_diameter = self._calculate_root_diameter(area, root_length)

                    # 计算根系体积和表面积
                    root_volume = self._calculate_root_volume(root_length, root_diameter)
                    root_surface = self._calculate_root_surface(root_length, root_diameter)

                    # 保存连通组件信息
                    self.connected_components.append({
                        'id': root_count,
                        'area_pixels': area,
                        'area_mm2': area * self.pixel_to_mm ** 2,
                        'length_pixels': root_length / self.pixel_to_mm,
                        'length_mm': root_length,
                        'diameter_mm': root_diameter,
                        'volume_mm3': root_volume,
                        'surface_mm2': root_surface,
                        'centroid': centroids[i],  # (x, y)坐标
                        'bounding_box': stats[i, :4],  # x, y, width, height
                        'label': i  # 在标签图像中的标签值
                    })

            self.root_count = root_count

            # 创建简单的彩色标注图用于显示
            self._create_simple_color_map(labels, num_labels)

            return True, f"检测到 {root_count} 个根系"

        except Exception as e:
            self.root_count = 0
            return False, f"根系计数失败: {str(e)}"

    def _calculate_root_length(self, root_mask):
        """计算根系长度（骨架长度）"""
        try:
            # 骨架化计算长度
            skeleton = morphology.skeletonize(root_mask > 0)
            skeleton_pixels = np.sum(skeleton)
            return skeleton_pixels * self.pixel_to_mm
        except:
            # 如果骨架化失败，使用面积估算长度
            area_pixels = np.sum(root_mask > 0)
            return np.sqrt(area_pixels) * self.pixel_to_mm

    def _calculate_root_diameter(self, area_pixels, length_mm):
        """计算根系直径"""
        try:
            if length_mm <= 0:
                return 0.0

            # 假设根系为圆柱体，直径 = 面积 / 长度
            area_mm2 = area_pixels * self.pixel_to_mm ** 2
            return area_mm2 / length_mm
        except:
            return 0.0

    def _calculate_root_volume(self, length_mm, diameter_mm):
        """计算根系体积"""
        try:
            if diameter_mm <= 0:
                return 0.0

            # 假设根系为圆柱体，体积 = π * (d/2)² * L
            radius = diameter_mm / 2
            return math.pi * radius * radius * length_mm
        except:
            return 0.0

    def _calculate_root_surface(self, length_mm, diameter_mm):
        """计算根系表面积"""
        try:
            if diameter_mm <= 0:
                return 0.0

            # 假设根系为圆柱体，表面积 = π * d * L
            return math.pi * diameter_mm * length_mm
        except:
            return 0.0

    def _create_simple_color_map(self, labels, num_labels):
        """创建简化的彩色标注图"""
        try:
            if num_labels <= 1:  # 只有背景
                return

            # 创建彩色图像
            height, width = labels.shape
            color_map = np.zeros((height, width, 3), dtype=np.uint8)

            # 为每个根系分配颜色（简化版）
            for i, component in enumerate(self.connected_components, 1):
                # 生成一致的颜色
                hue = (i * 137) % 360
                rgb = colorsys.hsv_to_rgb(hue / 360, 0.8, 1.0)
                color = [int(c * 255) for c in rgb]

                # 将该根系对应的区域着色
                mask = (labels == component['label'])
                color_map[mask] = color

            self.color_map = color_map

        except Exception as e:
            print(f"创建彩色标注图失败: {e}")

    def calculate_root_parameters(self):
        """计算根系参数：比根长、总根表面积、总根体积、总根长、根直径分布"""
        try:
            if not self.connected_components:
                return False, "没有根系数据，请先进行根系计数"

            # 初始化统计变量
            total_length = 0.0
            total_area = 0.0
            total_volume = 0.0
            total_surface = 0.0
            diameters = []

            # 统计所有根系
            for component in self.connected_components:
                total_length += component['length_mm']
                total_area += component['area_mm2']
                total_volume += component['volume_mm3']
                total_surface += component['surface_mm2']
                diameters.append(component['diameter_mm'])

            # 计算平均直径
            avg_diameter = np.mean(diameters) if diameters else 0.0

            # 计算比根长（总根长/总根系面积）
            specific_root_length = total_length / total_area if total_area > 0 else 0.0

            # 根据直径分级并计算体积占比
            diameter_distribution = self._classify_roots_by_diameter(diameters, self.connected_components)

            # 保存参数
            self.root_parameters = {
                'total_length': total_length,
                'total_area': total_area,
                'total_volume': total_volume,
                'total_surface': total_surface,
                'avg_diameter': avg_diameter,
                'specific_root_length': specific_root_length,
                'diameter_distribution': diameter_distribution
            }

            return True, "根系参数计算完成"
        except Exception as e:
            return False, f"根系参数计算失败: {str(e)}"

    def _classify_roots_by_diameter(self, diameters, components):
        """根据根直径对根系进行分级并计算体积占比（使用自定义或默认分级）"""
        try:
            # 初始化统计
            classification = {}
            total_volume = sum(c['volume_mm3'] for c in components)

            for class_name, min_d, max_d in self._get_diameter_classes():
                class_roots = []
                class_volume = 0.0
                class_count = 0

                for i, component in enumerate(components):
                    diameter = component['diameter_mm']
                    if max_d == float('inf'):
                        if diameter >= min_d:
                            in_range = True
                        else:
                            in_range = False
                    else:
                        in_range = (min_d <= diameter < max_d)

                    if in_range:
                        class_roots.append({
                            'id': component['id'],
                            'diameter': diameter,
                            'length': component['length_mm'],
                            'volume': component['volume_mm3']
                        })
                        class_volume += component['volume_mm3']
                        class_count += 1

                # 计算体积占比
                volume_percentage = (class_volume / total_volume * 100) if total_volume > 0 else 0

                classification[class_name] = {
                    'count': class_count,
                    'volume_mm3': round(class_volume, 3),
                    'volume_percentage': round(volume_percentage, 2),
                    'avg_diameter_mm': round(np.mean([r['diameter'] for r in class_roots]), 3) if class_roots else 0,
                    'min_diameter_mm': round(min([r['diameter'] for r in class_roots]), 3) if class_roots else 0,
                    'max_diameter_mm': round(max([r['diameter'] for r in class_roots]), 3) if class_roots else 0
                }

            return classification
        except Exception as e:
            print(f"根系分级失败: {e}")
            return {}

    def calculate_parameters(self):
        """计算根系参数（增强版）- 包含更多详细参数"""
        try:
            # 检查是否有过滤后的掩码
            if not hasattr(self, 'filtered_mask') or np.sum(self.filtered_mask) == 0:
                # 即使没有根系，也初始化所有字段为0或默认值
                self.results = {
                    '图像名称': self.image_name,
                    '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                    '像素转换系数(mm/像素)': self.pixel_to_mm,
                    '图像宽度(mm)': round(self.image_width * self.pixel_to_mm, 2),
                    '图像高度(mm)': round(self.image_height * self.pixel_to_mm, 2),
                    '根系数量': 0,
                    '总根长(mm)': 0.0,
                    '根系面积(mm²)': 0.0,
                    '图像宽度(像素)': self.image_width,
                    '图像高度(像素)': self.image_height,
                    '最大根系面积(mm²)': 0.0,
                    '最小根系面积(mm²)': 0.0,
                    '平均根系面积(mm²)': 0.0,
                    '面积标准差(mm²)': 0.0,
                    '面积变异系数(%)': 0.0,
                    '最大根系长度(mm)': 0.0,
                    '最小根系长度(mm)': 0.0,
                    '平均根系长度(mm)': 0.0,
                    '长度标准差(mm)': 0.0,
                    '最大根系直径(mm)': 0.0,
                    '最小根系直径(mm)': 0.0,
                    '平均根系直径(mm)': 0.0,
                    '直径标准差(mm)': 0.0,
                    '总根系体积(mm³)': 0.0,
                    '平均根系体积(mm³)': 0.0,
                    '总根系表面积(mm²)': 0.0,
                    '平均根系表面积(mm²)': 0.0,
                    '总根体积(mm³)': 0.0,
                    '总根表面积(mm²)': 0.0,
                    '比根长(mm/mm²)': 0.0,
                    '总根长(累计)(mm)': 0.0,
                    '平均根直径(mm)': 0.0
                }

                # 添加直径分级字段（即使为0也保留）
                for class_name, _, _ in self._get_diameter_classes():
                    self.results[f'{class_name}数量'] = 0
                    self.results[f'{class_name}体积(mm³)'] = 0.0
                    self.results[f'{class_name}体积占比(%)'] = 0.0
                    self.results[f'{class_name}平均直径(mm)'] = 0.0

                return True, "没有检测到根系，所有参数设置为0"

            # 计算总面积
            root_area_pixels = np.sum(self.filtered_mask > 0)
            root_area_mm2 = root_area_pixels * self.pixel_to_mm ** 2

            # 骨架化计算总长度
            binary_for_skeleton = self.filtered_mask > 0
            skeleton = morphology.skeletonize(binary_for_skeleton)
            skeleton_pixels = np.sum(skeleton)
            total_length_pixels = skeleton_pixels
            total_length_mm = total_length_pixels * self.pixel_to_mm

            # 保存整体结果
            self.results = {
                '图像名称': self.image_name,
                '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                '像素转换系数(mm/像素)': self.pixel_to_mm,
                '图像宽度(mm)': round(self.image_width * self.pixel_to_mm, 2),
                '图像高度(mm)': round(self.image_height * self.pixel_to_mm, 2),
                '根系数量': self.root_count,
                '总根长(mm)': round(total_length_mm, 2),
                '根系面积(mm²)': round(root_area_mm2, 2),
                '图像宽度(像素)': self.filtered_mask.shape[1],
                '图像高度(像素)': self.filtered_mask.shape[0]
            }

            # 如果有根系信息，添加尺寸分布
            if self.connected_components:
                areas = [c['area_mm2'] for c in self.connected_components]
                lengths = [c['length_mm'] for c in self.connected_components]
                diameters = [c['diameter_mm'] for c in self.connected_components]
                volumes = [c['volume_mm3'] for c in self.connected_components]
                surfaces = [c['surface_mm2'] for c in self.connected_components]

                self.results.update({
                    '最大根系面积(mm²)': round(max(areas), 2) if areas else 0.0,
                    '最小根系面积(mm²)': round(min(areas), 2) if areas else 0.0,
                    '平均根系面积(mm²)': round(np.mean(areas), 2) if areas else 0.0,
                    '面积标准差(mm²)': round(np.std(areas), 2) if areas else 0.0,
                    '面积变异系数(%)': round((np.std(areas) / np.mean(areas) * 100) if np.mean(areas) > 0 else 0, 2),
                    '最大根系长度(mm)': round(max(lengths), 2) if lengths else 0.0,
                    '最小根系长度(mm)': round(min(lengths), 2) if lengths else 0.0,
                    '平均根系长度(mm)': round(np.mean(lengths), 2) if lengths else 0.0,
                    '长度标准差(mm)': round(np.std(lengths), 2) if lengths else 0.0,
                    '最大根系直径(mm)': round(max(diameters), 3) if diameters else 0.0,
                    '最小根系直径(mm)': round(min(diameters), 3) if diameters else 0.0,
                    '平均根系直径(mm)': round(np.mean(diameters), 3) if diameters else 0.0,
                    '直径标准差(mm)': round(np.std(diameters), 3) if diameters else 0.0,
                    '总根系体积(mm³)': round(sum(volumes), 2) if volumes else 0.0,
                    '平均根系体积(mm³)': round(np.mean(volumes), 2) if volumes else 0.0,
                    '总根系表面积(mm²)': round(sum(surfaces), 2) if surfaces else 0.0,
                    '平均根系表面积(mm²)': round(np.mean(surfaces), 2) if surfaces else 0.0
                })
            else:
                # 即使没有根系组件，也添加这些字段为0
                self.results.update({
                    '最大根系面积(mm²)': 0.0,
                    '最小根系面积(mm²)': 0.0,
                    '平均根系面积(mm²)': 0.0,
                    '面积标准差(mm²)': 0.0,
                    '面积变异系数(%)': 0.0,
                    '最大根系长度(mm)': 0.0,
                    '最小根系长度(mm)': 0.0,
                    '平均根系长度(mm)': 0.0,
                    '长度标准差(mm)': 0.0,
                    '最大根系直径(mm)': 0.0,
                    '最小根系直径(mm)': 0.0,
                    '平均根系直径(mm)': 0.0,
                    '直径标准差(mm)': 0.0,
                    '总根系体积(mm³)': 0.0,
                    '平均根系体积(mm³)': 0.0,
                    '总根系表面积(mm²)': 0.0,
                    '平均根系表面积(mm²)': 0.0
                })

            # 添加根系参数
            if hasattr(self, 'root_parameters') and self.root_parameters:
                self.results.update({
                    '总根体积(mm³)': round(self.root_parameters['total_volume'], 2),
                    '总根表面积(mm²)': round(self.root_parameters['total_surface'], 2),
                    '比根长(mm/mm²)': round(self.root_parameters['specific_root_length'], 4),
                    '总根长(累计)(mm)': round(self.root_parameters['total_length'], 2),
                    '平均根直径(mm)': round(self.root_parameters['avg_diameter'], 3)
                })

                # 添加直径分级信息
                if 'diameter_distribution' in self.root_parameters:
                    dist = self.root_parameters['diameter_distribution']
                    for class_name, class_data in dist.items():
                        if class_data['count'] > 0:
                            self.results[f'{class_name}数量'] = class_data['count']
                            self.results[f'{class_name}体积(mm³)'] = round(class_data['volume_mm3'], 2)
                            self.results[f'{class_name}体积占比(%)'] = round(class_data['volume_percentage'], 2)
                            self.results[f'{class_name}平均直径(mm)'] = round(class_data['avg_diameter_mm'], 3)
            else:
                # 如果没有根系参数，添加默认值
                self.results.update({
                    '总根体积(mm³)': 0.0,
                    '总根表面积(mm²)': 0.0,
                    '比根长(mm/mm²)': 0.0,
                    '总根长(累计)(mm)': 0.0,
                    '平均根直径(mm)': 0.0
                })

            # 确保所有直径分级字段都存在，即使为0
            for class_name, _, _ in self._get_diameter_classes():
                if f'{class_name}数量' not in self.results:
                    self.results[f'{class_name}数量'] = 0
                if f'{class_name}体积(mm³)' not in self.results:
                    self.results[f'{class_name}体积(mm³)'] = 0.0
                if f'{class_name}体积占比(%)' not in self.results:
                    self.results[f'{class_name}体积占比(%)'] = 0.0
                if f'{class_name}平均直径(mm)' not in self.results:
                    self.results[f'{class_name}平均直径(mm)'] = 0.0

            return True, "参数计算完成"
        except Exception as e:
            return False, f"参数计算失败: {str(e)}"

    def set_scale_from_measurement(self, measured_length_mm, pixel_length):
        """通过已知测量设置比例尺"""
        try:
            if pixel_length <= 0:
                return False, "像素长度必须大于0"

            self.pixel_to_mm = measured_length_mm / pixel_length
            return True, f"比例设置成功: {self.pixel_to_mm:.4f} mm/像素"
        except Exception as e:
            return False, f"设置比例失败: {str(e)}"

    def set_scale_from_dimensions(self, width_mm, height_mm):
        """通过图像尺寸设置比例尺"""
        try:
            if width_mm <= 0 or height_mm <= 0:
                return False, "尺寸必须大于0"

            # 使用平均比例
            width_scale = width_mm / self.image_width
            height_scale = height_mm / self.image_height
            self.pixel_to_mm = (width_scale + height_scale) / 2

            return True, f"比例设置成功: {self.pixel_to_mm:.4f} mm/像素"
        except Exception as e:
            return False, f"设置比例失败: {str(e)}"

    def _draw_text_pil(self, image, text, position, font_size=18, color=(255, 255, 255)):
        """使用PIL绘制中文文本（替代cv2.putText，支持CJK字符）"""
        img_pil = Image.fromarray(cv2.cvtColor(image, cv2.COLOR_BGR2RGB))
        draw = ImageDraw.Draw(img_pil)
        font = ImageFont.truetype("C:/Windows/Fonts/simhei.ttf", font_size)
        draw.text(position, text, font=font, fill=color)
        return cv2.cvtColor(np.array(img_pil), cv2.COLOR_RGB2BGR)

    def _get_text_size_pil(self, text, font_size=18):
        """获取PIL文本尺寸"""
        font = ImageFont.truetype("C:/Windows/Fonts/simhei.ttf", font_size)
        bbox = font.getbbox(text)
        return bbox[2] - bbox[0], bbox[3] - bbox[1]

    def add_scale_bar(self, image, length_mm=10, position=(50, 50), color=(255, 255, 255), thickness=2):
        """在图像上添加比例尺"""
        try:
            # 计算比例尺的像素长度
            bar_length_pixels = int(length_mm / self.pixel_to_mm)

            # 绘制比例尺
            x, y = position
            cv2.rectangle(image,
                          (x, y - thickness - 5),
                          (x + bar_length_pixels, y + 15),
                          (0, 0, 0), -1)

            cv2.line(image,
                     (x, y),
                     (x + bar_length_pixels, y),
                     color, thickness)

            # 使用PIL绘制文本（支持中文）
            label = f"{length_mm} mm"
            text_w, text_h = self._get_text_size_pil(label, font_size=14)
            text_x = x + (bar_length_pixels - text_w) // 2
            image = self._draw_text_pil(image, label, (text_x, y + 15), font_size=14, color=color)

            return image
        except Exception as e:
            print(f"添加比例尺失败: {e}")
            return image

    def generate_detailed_report_image(self, output_path, show_scale=True):
        """生成详细分析报告图像"""
        try:
            fig = plt.figure(figsize=(18, 12))
            fig.suptitle(f'根系详细分析报告 - {self.image_name}', fontsize=18, fontweight='bold')

            # 创建子图布局
            gs = fig.add_gridspec(3, 4, hspace=0.3, wspace=0.3)

            # 1. 原始图像
            ax1 = fig.add_subplot(gs[0, 0])
            ax1.imshow(cv2.cvtColor(self.original_image, cv2.COLOR_BGR2RGB))
            ax1.set_title('原始图像', fontsize=12, fontweight='bold')
            ax1.axis('off')

            # 添加图像尺寸信息
            info_text = f'尺寸: {self.image_width}×{self.image_height} 像素\n'
            info_text += f'实际: {self.image_width * self.pixel_to_mm:.1f}×{self.image_height * self.pixel_to_mm:.1f} mm'
            ax1.text(0.02, 0.98, info_text, transform=ax1.transAxes,
                     fontsize=8, color='white',
                     verticalalignment='top',
                     bbox=dict(boxstyle='round', facecolor='black', alpha=0.5))

            # 2. 增强图像
            ax2 = fig.add_subplot(gs[0, 1])
            # 根据是否为扫描图像选择显示方式
            if self.use_scan_optimization and hasattr(self, 'scan_enhanced'):
                ax2.imshow(self.scan_enhanced, cmap='gray')
                ax2.set_title('扫描图像增强', fontsize=12, fontweight='bold')
            else:
                ax2.imshow(self.enhanced_image, cmap='gray')
                ax2.set_title('对比度增强', fontsize=12, fontweight='bold')
            ax2.axis('off')

            # 3. 分割结果
            ax3 = fig.add_subplot(gs[0, 2])
            if hasattr(self, 'binary_mask'):
                ax3.imshow(self.binary_mask, cmap='gray')
                method_title = '扫描图像分割' if self.use_scan_optimization else '分割结果（大津法）'
                ax3.set_title(method_title, fontsize=12, fontweight='bold')
                ax3.axis('off')
                ax3.text(0.02, 0.98, f'区域数: {self.filtered_count}',
                         transform=ax3.transAxes, fontsize=8, color='white',
                         verticalalignment='top',
                         bbox=dict(boxstyle='round', facecolor='black', alpha=0.5))

            # 4. 过滤结果
            ax4 = fig.add_subplot(gs[0, 3])
            if hasattr(self, 'filtered_mask'):
                ax4.imshow(self.filtered_mask, cmap='gray')
                filter_title = '扫描图像过滤' if self.use_scan_optimization else '过滤结果'
                ax4.set_title(filter_title, fontsize=12, fontweight='bold')
                ax4.axis('off')
                filter_info = f"过滤后: {self.filtered_count}个"
                if self.use_scan_optimization:
                    filter_info += " (扫描优化)"
                ax4.text(0.02, 0.98, filter_info,
                         transform=ax4.transAxes, fontsize=8, color='white',
                         verticalalignment='top',
                         bbox=dict(boxstyle='round', facecolor='blue', alpha=0.5))

            # 5. 根系计数结果
            ax5 = fig.add_subplot(gs[1, :2])
            if hasattr(self, 'color_map'):
                ax5.imshow(self.color_map)
                ax5.set_title(f'根系计数 ({self.root_count}个)', fontsize=12, fontweight='bold')
                ax5.axis('off')

            # 6. 结果叠加
            ax6 = fig.add_subplot(gs[1, 2:])
            if hasattr(self, 'filtered_mask'):
                overlay = self.original_image.copy()
                overlay[self.filtered_mask > 0] = [0, 255, 0]

                # 添加比例尺
                if show_scale:
                    overlay = self.add_scale_bar(overlay, length_mm=self.scale_bar_length_mm)

                ax6.imshow(cv2.cvtColor(overlay, cv2.COLOR_BGR2RGB))
                ax6.set_title('检测结果叠加', fontsize=12, fontweight='bold')
                ax6.axis('off')

                # 添加参数摘要
                if self.results:
                    summary = f"根系数量: {self.results.get('根系数量', 0)}\n"
                    summary += f"总根长: {self.results.get('总根长(mm)', 0):.1f} mm\n"
                    summary += f"根系面积: {self.results.get('根系面积(mm²)', 0):.1f} mm²\n"
                    summary += f"总根体积: {self.results.get('总根体积(mm³)', 0):.1f} mm³"
                    ax6.text(0.02, 0.98, summary, transform=ax6.transAxes,
                             fontsize=8, color='white',
                             verticalalignment='top',
                             bbox=dict(boxstyle='round', facecolor='green', alpha=0.7))

            # 7. 直径分布柱状图
            ax7 = fig.add_subplot(gs[2, 0])
            if hasattr(self, 'root_parameters') and 'diameter_distribution' in self.root_parameters:
                dist = self.root_parameters['diameter_distribution']
                classes = list(dist.keys())
                volumes = [dist[c]['volume_mm3'] for c in classes]
                percentages = [dist[c]['volume_percentage'] for c in classes]

                color_cycle = ['#ff9999', '#66b3ff', '#99ff99', '#ffcc99', '#c2c2f0',
                               '#ffb3e6', '#c2f0c2', '#ffccb3', '#b3b3ff', '#ffb366']
                colors = list(itertools.islice(itertools.cycle(color_cycle), len(classes)))
                bars = ax7.bar(classes, volumes, color=colors)
                ax7.set_title('根系直径分级体积分布', fontsize=12, fontweight='bold')
                ax7.set_ylabel('体积 (mm³)', fontsize=10)
                ax7.tick_params(axis='x', rotation=45)

                # 在柱状图上添加百分比标签
                for bar, percentage in zip(bars, percentages):
                    height = bar.get_height()
                    ax7.text(bar.get_x() + bar.get_width() / 2., height + max(volumes) * 0.01,
                             f'{percentage}%', ha='center', va='bottom', fontsize=9)

            # 8. 根系参数汇总表
            ax8 = fig.add_subplot(gs[2, 1:])
            ax8.axis('off')

            if hasattr(self, 'root_parameters') and self.root_parameters:
                # 创建参数表格
                params_data = [
                    ['参数', '数值', '单位'],
                    ['总根长', f"{self.root_parameters['total_length']:.1f}", 'mm'],
                    ['根系面积', f"{self.root_parameters['total_area']:.1f}", 'mm²'],
                    ['总根体积', f"{self.root_parameters['total_volume']:.1f}", 'mm³'],
                    ['总根表面积', f"{self.root_parameters['total_surface']:.1f}", 'mm²'],
                    ['平均根直径', f"{self.root_parameters['avg_diameter']:.3f}", 'mm'],
                    ['比根长', f"{self.root_parameters['specific_root_length']:.4f}", 'mm/mm²']
                ]

                table = ax8.table(cellText=params_data, loc='center', cellLoc='center')
                table.auto_set_font_size(False)
                table.set_fontsize(9)
                table.scale(1, 1.5)
                ax8.set_title('根系参数汇总', fontsize=12, fontweight='bold')

            plt.tight_layout(rect=[0, 0, 1, 0.96])
            plt.savefig(output_path, dpi=200, bbox_inches='tight', facecolor='white')
            plt.close()

            return True, "详细报告图像生成成功"
        except Exception as e:
            return False, f"报告图像生成失败: {str(e)}"

    def export_overlay_image(self, output_path, show_scale=True):
        """导出叠加结果图"""
        try:
            if not hasattr(self, 'filtered_mask'):
                return False, "没有可导出的结果"

            # 创建叠加图像
            overlay = self.original_image.copy()

            # 绘制检测到的根系
            overlay[self.filtered_mask > 0] = [0, 255, 0]

            # 添加比例尺
            if show_scale:
                overlay = self.add_scale_bar(overlay, length_mm=self.scale_bar_length_mm)

            # 使用PIL绘制中文文本
            scan_info = " [扫描优化]" if self.use_scan_optimization else ""
            info_text = f"{self.image_name} | 根系数量: {self.root_count}{scan_info} | {datetime.now().strftime('%Y-%m-%d %H:%M')}"
            overlay = self._draw_text_pil(overlay, info_text, (10, 10), font_size=18)

            # 添加参数信息
            if hasattr(self, 'root_parameters'):
                param_text = f"总根长: {self.root_parameters['total_length']:.1f}mm | "
                param_text += f"体积: {self.root_parameters['total_volume']:.1f}mm³"
                overlay = self._draw_text_pil(overlay, param_text, (10, 38), font_size=16)

            # 保存图像
            cv2.imwrite(output_path, overlay)
            return True, "叠加图像导出成功"
        except Exception as e:
            return False, f"叠加图像导出失败: {str(e)}"

    def save_results_csv(self, output_path):
        """保存结果为CSV - 增强版，输出所有根系参数"""
        try:
            # 定义所有可能的字段，确保即使值为0也保留
            all_fields = [
                '图像名称', '分析时间', '像素转换系数(mm/像素)', '图像宽度(mm)', '图像高度(mm)',
                '根系数量', '总根长(mm)', '根系面积(mm²)', '图像宽度(像素)', '图像高度(像素)',
                '最大根系面积(mm²)', '最小根系面积(mm²)', '平均根系面积(mm²)', '面积标准差(mm²)', '面积变异系数(%)',
                '最大根系长度(mm)', '最小根系长度(mm)', '平均根系长度(mm)', '长度标准差(mm)',
                '最大根系直径(mm)', '最小根系直径(mm)', '平均根系直径(mm)', '直径标准差(mm)',
                '总根系体积(mm³)', '平均根系体积(mm³)', '总根系表面积(mm²)', '平均根系表面积(mm²)',
                '总根体积(mm³)', '总根表面积(mm²)', '比根长(mm/mm²)', '总根长(累计)(mm)', '平均根直径(mm)',
            ]
            # 动态添加直径分级字段
            for class_name, _, _ in self._get_diameter_classes():
                keys = self._get_class_suffix_keys(class_name)
                all_fields.extend([keys['count'], keys['volume'], keys['volume_pct'], keys['avg_diam']])
            all_fields.extend(['分析类型', '扫描优化'])

            # 准备数据 - 确保所有字段都存在，即使值为0
            data = {}
            for field in all_fields:
                if field in self.results:
                    data[field] = self.results[field]
                elif field == '分析类型':
                    data[field] = '总体'
                elif field == '扫描优化':
                    data[field] = '是' if self.use_scan_optimization else '否'
                else:
                    # 对于数值字段，设置为0
                    if '数量' in field or '体积' in field or '面积' in field or '长度' in field or '直径' in field or '比根长' in field:
                        data[field] = 0.0
                    elif '占比' in field:
                        data[field] = 0.0
                    else:
                        data[field] = ''

            # 如果文件存在，追加模式；否则创建新文件
            file_exists = os.path.isfile(output_path)

            with open(output_path, 'a', newline='', encoding='utf-8-sig') as f:
                writer = csv.DictWriter(f, fieldnames=all_fields)
                if not file_exists:
                    writer.writeheader()
                writer.writerow(data)

            # 保存根系分级详细数据
            if hasattr(self, 'root_parameters') and 'diameter_distribution' in self.root_parameters:
                detail_path = output_path.replace('.csv', '_分级详细.csv')
                with open(detail_path, 'w', newline='', encoding='utf-8-sig') as f:
                    writer = csv.writer(f)
                    writer.writerow(['根系直径分级详细报告'])
                    writer.writerow(['图像名称', self.image_name])
                    writer.writerow(['分析时间', datetime.now().strftime('%Y-%m-%d %H:%M:%S')])
                    writer.writerow(['扫描优化', '是' if self.use_scan_optimization else '否'])
                    writer.writerow([])

                    writer.writerow(['直径分级', '数量', '体积(mm³)', '体积占比(%)',
                                     '平均直径(mm)', '最小直径(mm)', '最大直径(mm)'])

                    dist = self.root_parameters['diameter_distribution']
                    for class_name, _, _ in self._get_diameter_classes():
                        class_data = dist.get(class_name, {
                            'count': 0,
                            'volume_mm3': 0.0,
                            'volume_percentage': 0.0,
                            'avg_diameter_mm': 0.0,
                            'min_diameter_mm': 0.0,
                            'max_diameter_mm': 0.0
                        })
                        writer.writerow([
                            class_name,
                            class_data['count'],
                            round(class_data['volume_mm3'], 3),
                            round(class_data['volume_percentage'], 2),
                            round(class_data['avg_diameter_mm'], 3),
                            round(class_data['min_diameter_mm'], 3),
                            round(class_data['max_diameter_mm'], 3)
                        ])

                    # 添加汇总
                    writer.writerow([])
                    writer.writerow(['参数汇总'])
                    writer.writerow(['总根系数量', self.root_count])
                    writer.writerow(['总根体积(mm³)', round(self.root_parameters.get('total_volume', 0), 2)])
                    writer.writerow(['总根长(mm)', round(self.root_parameters.get('total_length', 0), 2)])
                    writer.writerow(['总根表面积(mm²)', round(self.root_parameters.get('total_surface', 0), 2)])
                    writer.writerow(['平均根直径(mm)', round(self.root_parameters.get('avg_diameter', 0), 3)])
                    writer.writerow(['根系面积(mm²)', round(self.root_parameters.get('total_area', 0), 2)])
                    writer.writerow(['比根长(mm/mm²)', round(self.root_parameters.get('specific_root_length', 0), 4)])

                    # 添加尺寸分布信息
                    writer.writerow([])
                    writer.writerow(['尺寸分布统计'])
                    writer.writerow(['最大根系面积(mm²)', self.results.get('最大根系面积(mm²)', 0)])
                    writer.writerow(['最小根系面积(mm²)', self.results.get('最小根系面积(mm²)', 0)])
                    writer.writerow(['平均根系面积(mm²)', self.results.get('平均根系面积(mm²)', 0)])
                    writer.writerow(['面积标准差(mm²)', self.results.get('面积标准差(mm²)', 0)])
                    writer.writerow(['面积变异系数(%)', self.results.get('面积变异系数(%)', 0)])
                    writer.writerow(['最大根系长度(mm)', self.results.get('最大根系长度(mm)', 0)])
                    writer.writerow(['最小根系长度(mm)', self.results.get('最小根系长度(mm)', 0)])
                    writer.writerow(['平均根系长度(mm)', self.results.get('平均根系长度(mm)', 0)])
                    writer.writerow(['长度标准差(mm)', self.results.get('长度标准差(mm)', 0)])
                    writer.writerow(['最大根系直径(mm)', self.results.get('最大根系直径(mm)', 0)])
                    writer.writerow(['最小根系直径(mm)', self.results.get('最小根系直径(mm)', 0)])
                    writer.writerow(['直径标准差(mm)', self.results.get('直径标准差(mm)', 0)])
                    writer.writerow(['总根系体积(mm³)', self.results.get('总根系体积(mm³)', 0)])
                    writer.writerow(['平均根系体积(mm³)', self.results.get('平均根系体积(mm³)', 0)])
                    writer.writerow(['总根系表面积(mm²)', self.results.get('总根系表面积(mm²)', 0)])
                    writer.writerow(['平均根系表面积(mm²)', self.results.get('平均根系表面积(mm²)', 0)])

            return True, "CSV保存成功"
        except Exception as e:
            return False, f"CSV保存失败: {str(e)}"

    def save_results_json(self, output_path):
        """保存结果为JSON"""
        try:
            # 读取现有数据或创建新列表
            if os.path.exists(output_path):
                with open(output_path, 'r', encoding='utf-8') as f:
                    data = json.load(f)
            else:
                data = []

            # 创建完整结果
            complete_result = {
                '总体结果': self.results,
                '根系参数': self.root_parameters,
                '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S'),
                '图像信息': {
                    '文件名': self.image_name,
                    '尺寸_像素': f"{self.image_width}x{self.image_height}",
                    '尺寸_mm': f"{self.image_width * self.pixel_to_mm:.1f}x{self.image_height * self.pixel_to_mm:.1f}",
                    '像素转换系数': self.pixel_to_mm
                },
                '扫描优化': self.use_scan_optimization,
                '扫描参数': self.scan_params if self.use_scan_optimization else None
            }

            # 添加新结果
            data.append(complete_result)

            # 保存
            with open(output_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)
            return True, "JSON保存成功"
        except Exception as e:
            return False, f"JSON保存失败: {str(e)}"

    # 静态方法用于并行处理
    @staticmethod
    def analyze_single_image_static(params):
        """
        静态方法：分析单个图像（用于多进程）
        参数params是一个包含所有必要参数的字典
        返回: (成功标志, 结果字典, 错误信息)
        """
        try:
            # 记录内存使用情况
            process = psutil.Process(os.getpid())
            initial_memory = process.memory_info().rss / 1024 / 1024  # MB

            image_path = params['image_path']
            pixel_to_mm = params['pixel_to_mm']
            seg_method = params['seg_method']
            min_length = params['min_length']
            min_area = params['min_area']
            min_aspect_ratio = params['min_aspect_ratio']
            min_root_size = params['min_root_size']
            output_dir = params.get('output_dir', os.path.dirname(image_path))
            use_scan_optimization = params.get('use_scan_optimization', False)
            scan_background_type = params.get('scan_background_type', 'auto')
            scan_quality = params.get('scan_quality', 'auto')
            roi_active = params.get('roi_active', None)

            # 创建分析器实例
            analyzer = RootSystemAnalyzer(pixel_to_mm)
            analyzer.roi_active = roi_active
            if params.get('diameter_classes') is not None:
                analyzer.diameter_classes = params['diameter_classes']

            # 设置扫描优化参数
            if use_scan_optimization:
                analyzer.enable_scan_optimization(True)
                analyzer.set_scan_background_type(scan_background_type)
                analyzer.set_scan_quality(scan_quality)

            # 加载图像
            success, message = analyzer.load_image(image_path)
            if not success:
                return False, {}, message

            # 分割 - 仅使用大津法或扫描优化
            success, message = analyzer.segment_roots(method='otsu')
            if not success:
                return False, {}, message

            # 过滤
            success, message = analyzer.filter_non_roots(
                min_length=min_length,
                min_area=min_area,
                min_aspect_ratio=min_aspect_ratio
            )
            if not success:
                return False, {}, message

            # 计数根系
            success, message = analyzer.count_roots(min_size=min_root_size)
            if not success:
                return False, {}, message

            # 计算根系参数
            success, message = analyzer.calculate_root_parameters()
            if not success:
                return False, {}, message

            # 计算所有参数
            success, message = analyzer.calculate_parameters()
            if not success:
                return False, {}, message

            # 准备结果
            result = {
                'success': True,
                'analyzer': analyzer,
                'image_name': analyzer.image_name,
                'results': analyzer.results.copy(),
                'root_parameters': analyzer.root_parameters.copy(),
                'filter_stats': analyzer.filter_stats.copy(),
                'root_count': analyzer.root_count,
                'total_length': analyzer.root_parameters.get('total_length', 0),
                'total_area': analyzer.root_parameters.get('total_area', 0),
                'total_volume': analyzer.root_parameters.get('total_volume', 0),
                'use_scan_optimization': use_scan_optimization
            }

            # 为每个图像生成叠加图 - 关键修复
            try:
                # 确保输出目录存在
                os.makedirs(output_dir, exist_ok=True)

                # 生成叠加图
                base_name = os.path.splitext(os.path.basename(image_path))[0]
                timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
                overlay_path = os.path.join(output_dir, f"{base_name}_结果叠加_{timestamp}.png")

                # 检查是否有过滤后的掩码
                if hasattr(analyzer, 'filtered_mask') and np.sum(analyzer.filtered_mask) > 0:
                    # 生成叠加图像
                    overlay = analyzer.original_image.copy()
                    overlay[analyzer.filtered_mask > 0] = [0, 255, 0]

                    # 使用PIL绘制中文文本
                    scan_info = " [扫描优化]" if use_scan_optimization else ""
                    info_text = f"{analyzer.image_name} | 根系数量: {analyzer.root_count}{scan_info} | {datetime.now().strftime('%Y-%m-%d %H:%M')}"
                    overlay = analyzer._draw_text_pil(overlay, info_text, (10, 10), font_size=18)

                    # 保存图像
                    cv2.imwrite(overlay_path, overlay)
                    result['overlay_path'] = overlay_path
                    print(f"已生成叠加图: {overlay_path}")
                else:
                    print(f"没有检测到根系，跳过叠加图生成: {image_path}")
                    result['overlay_path'] = None
            except Exception as e:
                print(f"生成叠加图失败: {e}")
                result['overlay_path'] = None

            # 清理分析器中的大对象以节省内存
            for attr in ['original_image', 'enhanced_image', 'binary_mask',
                         'filtered_mask', 'color_map', 'gray_image', 'display_image']:
                if hasattr(analyzer, attr):
                    setattr(analyzer, attr, None)

            # 强制垃圾回收
            gc.collect()

            # 记录最终内存使用
            final_memory = process.memory_info().rss / 1024 / 1024  # MB
            memory_used = final_memory - initial_memory
            print(f"进程 {os.getpid()} 内存使用: {initial_memory:.1f}MB -> {final_memory:.1f}MB (Δ{memory_used:.1f}MB)")

            return True, result, "分析成功"

        except Exception as e:
            return False, {}, f"分析失败: {str(e)}"


class CollapsiblePane(ttk.LabelFrame):
    """可折叠面板"""

    def __init__(self, parent, text="", *args, **kwargs):
        ttk.LabelFrame.__init__(self, parent, text=text, *args, **kwargs)

        self.expanded = True
        self.content_area = None

        # 创建标题按钮
        self.toggle_button = ttk.Button(self, text="▼ " + text,
                                        command=self.toggle,
                                        style="Toggle.TButton")
        self.toggle_button.grid(row=0, column=0, sticky="ew", padx=5, pady=2)

        # 创建内容区域
        self.content_area = ttk.Frame(self)
        self.content_area.grid(row=1, column=0, sticky="nsew", padx=5, pady=(0, 5))

        self.columnconfigure(0, weight=1)
        self.content_area.columnconfigure(0, weight=1)

        # 隐藏内容区域（默认展开）
        self.content_area.grid_remove()
        self.toggle_button.configure(text="▶ " + text)
        self.expanded = False

    def toggle(self):
        """切换面板展开/折叠状态"""
        if self.expanded:
            self.content_area.grid_remove()
            self.toggle_button.configure(text="▶ " + self.toggle_button.cget("text")[2:])
        else:
            self.content_area.grid()
            self.toggle_button.configure(text="▼ " + self.toggle_button.cget("text")[2:])

        self.expanded = not self.expanded

    def add_widgets(self, widgets_func):
        """添加小部件到内容区域"""
        widgets_func(self.content_area)


class RootAnalysisApp:
    """根系分析应用程序"""

    def __init__(self, root):
        self.root = root
        self.root.title("根图分析 - RootVision")
        self.root.geometry("1500x900")

        # 设置最小窗口尺寸
        self.root.minsize(1300, 750)

        # 设置窗口图标
        self.set_window_icon()

        # 初始化分析器
        self.analyzer = RootSystemAnalyzer()

        # 自定义直径分级（默认使用标准5级）
        self.diameter_classes = list(RootSystemAnalyzer.DEFAULT_DIAMETER_CLASSES)

        # 状态变量
        self.current_image_path = None
        self.output_dir = None
        self.processing = False
        self.queue = queue.Queue()
        self.batch_files = []

        # 图像缩放相关
        self.zoom_level = 1.0
        self.zoom_step = 0.1
        self.max_zoom = 5.0
        self.min_zoom = 0.1
        self.pan_x = 0
        self.pan_y = 0
        self.pan_start_x = 0
        self.pan_start_y = 0
        self.panning = False

        # 当前显示的图像类型
        self.current_image_type = '原始图'

        # 并行处理相关参数 - 限制最大并行数量为5
        self.max_workers = 5  # 固定设置为5，限制并行处理上限
        self.batch_timeout = 660  # 单个图像最大处理时间(秒)
        self.batch_results = []  # 批量处理结果

        # 扫描图像优化相关
        self.scan_optimization_enabled = False
        self.scan_background_type = 'auto'
        self.scan_quality = 'auto'

        # 参数变量（原 create_param_controls 初始化）
        self.param_vars = {}
        self.param_vars['pixel_to_mm'] = tk.DoubleVar(value=0.1)
        self.param_vars['min_length'] = tk.IntVar(value=5)
        self.param_vars['min_area'] = tk.IntVar(value=20)
        self.param_vars['min_aspect_ratio'] = tk.DoubleVar(value=1.0)
        self.min_root_size_var = tk.IntVar(value=20)

        # 参照物选取模式
        self.ref_select_mode = False
        self.ref_start_point = None
        self.ref_end_point = None
        self.ref_line_id = None

        # ROI 框选模式
        self.roi_select_mode = False
        self.roi_start = None
        self.roi_end = None
        self.roi_rect_id = None
        self.roi_active = None  # (x1,y1,x2,y2) 图像坐标, None=未激活

        # 输出选项
        self.save_csv_var = tk.BooleanVar(value=True)
        self.save_json_var = tk.BooleanVar(value=True)
        self.save_overlay_var = tk.BooleanVar(value=True)
        self.save_report_var = tk.BooleanVar(value=False)
        self.show_scale_var = tk.BooleanVar(value=True)

        # 创建菜单栏
        self.create_menubar()

        # 创建GUI
        self.create_widgets()

        # 启动队列处理器
        self.root.after(100, self.process_queue)

        # 加载上次的配置
        self.load_config()

        # 绑定鼠标事件
        self.bind_events()

    def set_window_icon(self):
        """设置窗口图标"""
        try:
            # 创建简单图标
            icon_data = """
            R0lGODlhEAAQAIAAAAAAAP///yH5BAAAAAAALAAAAAAQABAAAAIfhG+gr5rJ2Iqz
            /mCHtJdY1gxm1zXm9nWq+LXmNj6XGZYQAQA7
            """
            # 简化：使用默认图标
            pass
        except:
            pass

    def create_menubar(self):
        """创建菜单栏"""
        menubar = tk.Menu(self.root)
        self.root.config(menu=menubar)

        # 文件菜单
        file_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="文件", menu=file_menu)
        file_menu.add_command(label="打开图像", command=self.select_image, accelerator="Ctrl+O")
        file_menu.add_command(label="批量选择图像", command=self.select_images_batch, accelerator="Ctrl+Shift+O")
        file_menu.add_separator()
        file_menu.add_command(label="选择输出目录", command=self.select_output_dir)
        file_menu.add_separator()
        file_menu.add_command(label="退出", command=self.root.quit, accelerator="Ctrl+Q")

        # 分析菜单
        analysis_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="分析", menu=analysis_menu)
        analysis_menu.add_command(label="开始分析", command=self.start_analysis, accelerator="Ctrl+A")
        analysis_menu.add_command(label="计数根系", command=self.count_roots)
        analysis_menu.add_command(label="计算参数", command=self.calculate_parameters)
        analysis_menu.add_separator()
        analysis_menu.add_command(label="批量分析", command=self.batch_analysis)
        analysis_menu.add_command(label="并行批量分析", command=self.parallel_batch_analysis, accelerator="Ctrl+P")

        # 结果菜单
        results_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="结果", menu=results_menu)
        results_menu.add_command(label="显示直径分级详情", command=self.show_diameter_distribution)
        results_menu.add_command(label="显示过滤统计", command=self.show_filter_stats)
        results_menu.add_separator()
        results_menu.add_command(label="导出结果图", command=self.export_result_image)
        results_menu.add_command(label="导出数据", command=self.export_results)
        results_menu.add_command(label="复制结果", command=self.copy_results, accelerator="Ctrl+C")

        # 视图菜单
        view_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="视图", menu=view_menu)

        # 图像类型子菜单
        image_type_menu = tk.Menu(view_menu, tearoff=0)
        view_menu.add_cascade(label="图像显示类型", menu=image_type_menu)

        self.image_type_var = tk.StringVar(value='原始图')
        preview_types = ['原始图', '增强图', '分割图', '过滤图', '根系计数', '结果图']
        for preview_type in preview_types:
            image_type_menu.add_radiobutton(
                label=preview_type,
                variable=self.image_type_var,
                value=preview_type,
                command=lambda pt=preview_type: self.show_image(pt)
            )

        # 缩放控制子菜单
        zoom_menu = tk.Menu(view_menu, tearoff=0)
        view_menu.add_cascade(label="缩放控制", menu=zoom_menu)
        zoom_menu.add_command(label="放大", command=self.zoom_in, accelerator="Ctrl++")
        zoom_menu.add_command(label="缩小", command=self.zoom_out, accelerator="Ctrl+-")
        zoom_menu.add_command(label="重置缩放", command=self.zoom_reset, accelerator="Ctrl+0")
        zoom_menu.add_command(label="适应窗口", command=self.fit_to_window, accelerator="Ctrl+F")

        # 设置菜单
        settings_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="设置", menu=settings_menu)

        # 扫描优化子菜单
        scan_menu = tk.Menu(settings_menu, tearoff=0)
        settings_menu.add_cascade(label="扫描图像优化", menu=scan_menu)

        self.scan_optimization_var = tk.BooleanVar(value=False)
        scan_menu.add_checkbutton(
            label="启用扫描图像优化",
            variable=self.scan_optimization_var,
            command=self.toggle_scan_optimization
        )

        # 背景类型子菜单
        bg_type_menu = tk.Menu(scan_menu, tearoff=0)
        scan_menu.add_cascade(label="背景类型", menu=bg_type_menu)

        self.scan_background_type_var = tk.StringVar(value='auto')
        bg_types = ['auto', 'light', 'dark']
        for bg_type in bg_types:
            bg_type_menu.add_radiobutton(
                label=bg_type,
                variable=self.scan_background_type_var,
                value=bg_type,
                command=self.toggle_scan_optimization
            )

        # 扫描质量子菜单
        quality_menu = tk.Menu(scan_menu, tearoff=0)
        scan_menu.add_cascade(label="扫描质量", menu=quality_menu)

        self.scan_quality_var = tk.StringVar(value='auto')
        qualities = ['auto', 'high', 'medium', 'low']
        for quality in qualities:
            quality_menu.add_radiobutton(
                label=quality,
                variable=self.scan_quality_var,
                value=quality,
                command=self.toggle_scan_optimization
            )

        # 帮助菜单
        help_menu = tk.Menu(menubar, tearoff=0)
        menubar.add_cascade(label="帮助", menu=help_menu)
        help_menu.add_command(label="关于", command=self.show_about)
        help_menu.add_command(label="使用说明", command=self.show_help)

        # 添加快捷键绑定
        self.root.bind("<Control-o>", lambda e: self.select_image())
        self.root.bind("<Control-Shift-O>", lambda e: self.select_images_batch())
        self.root.bind("<Control-a>", lambda e: self.start_analysis())
        self.root.bind("<Control-p>", lambda e: self.parallel_batch_analysis())
        self.root.bind("<Control-c>", lambda e: self.copy_results())
        self.root.bind("<Control-plus>", lambda e: self.zoom_in())
        self.root.bind("<Control-minus>", lambda e: self.zoom_out())
        self.root.bind("<Control-0>", lambda e: self.zoom_reset())
        self.root.bind("<Control-f>", lambda e: self.fit_to_window())

    def show_about(self):
        """显示关于对话框"""
        about_text = """根图分析 - RootVision v1.0

功能特点：
1. 支持单个和批量根系图像分析
2. 自动检测和优化扫描图像
3. 并行处理加速批量分析
4. 详细的根系参数计算和分级统计
5. 多种结果导出格式

开发者：根系分析团队
版权所有 © 2024"""

        messagebox.showinfo("关于", about_text)

    def show_help(self):
        """显示使用说明"""
        help_text = """使用说明：

基本操作：
1. 通过"文件"菜单或按钮选择图像
2. 设置比例尺（三种方式）：
   - 通过测量：输入已知长度(mm)和对应像素数
   - 通过图像尺寸：输入图像实际宽高(mm)
   - 通过DPI：输入扫描分辨率DPI自动转换(1 inch = 25.4 mm)
   - 通过参照物：点击"选取参照物"，在图像上拖拽画线，输入实际长度
3. 点击"开始分析"进行分析
4. 查看右侧的分析结果

批量处理：
1. 通过"批量选择"添加多个图像
2. 点击"批量分析"或"并行批量分析"
3. 查看批量处理结果

扫描图像优化：
1. 对于扫描图像，启用扫描优化
2. 根据图像特点设置背景类型和质量
3. 系统会自动优化处理流程

结果导出：
1. 分析后可导出图像结果
2. 支持CSV、JSON、TXT格式数据导出
3. 可生成详细分析报告图"""

        help_window = tk.Toplevel(self.root)
        help_window.title("使用说明")
        help_window.geometry("600x500")

        text_area = scrolledtext.ScrolledText(help_window, width=70, height=30,
                                              font=("Arial", 10))
        text_area.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)
        text_area.insert(tk.END, help_text)
        text_area.config(state=tk.DISABLED)

        ttk.Button(help_window, text="关闭", command=help_window.destroy).pack(pady=10)

    def create_widgets(self):
        """创建GUI组件"""
        # 创建主框架
        main_frame = ttk.Frame(self.root, padding="5")
        main_frame.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

        # 配置网格权重 - 调整列权重，使图像预览区域更大
        self.root.columnconfigure(0, weight=1)
        self.root.rowconfigure(0, weight=1)
        main_frame.columnconfigure(0, weight=0)  # 控制面板
        main_frame.columnconfigure(1, weight=3)  # 图像预览区域（增大）
        main_frame.columnconfigure(2, weight=1)  # 结果区域（减小）
        main_frame.rowconfigure(0, weight=1)
        main_frame.rowconfigure(1, weight=0)

        # 标题
        title_label = ttk.Label(
            main_frame,
            text="🌱 根图分析 - RootVision v1.0",
            font=("Arial", 16, "bold")
        )
        title_label.grid(row=0, column=0, columnspan=3, pady=(0, 5))

        # 左侧控制面板 - 使用可折叠面板
        left_panel = ttk.Frame(main_frame, padding="5")
        left_panel.grid(row=1, column=0, sticky=(tk.N, tk.S, tk.W), padx=(0, 5))

        # 创建垂直滚动条
        left_canvas = tk.Canvas(left_panel, width=320, height=700)
        scrollbar = ttk.Scrollbar(left_panel, orient=tk.VERTICAL, command=left_canvas.yview)
        scrollable_frame = ttk.Frame(left_canvas)

        scrollable_frame.bind(
            "<Configure>",
            lambda e: left_canvas.configure(scrollregion=left_canvas.bbox("all"))
        )

        left_canvas.create_window((0, 0), window=scrollable_frame, anchor="nw")
        left_canvas.configure(yscrollcommand=scrollbar.set)

        left_canvas.pack(side="left", fill="both", expand=True)
        scrollbar.pack(side="right", fill="y")

        # 图像操作面板
        image_pane = CollapsiblePane(scrollable_frame, text="图像操作", padding="5")
        image_pane.grid(row=0, column=0, sticky="ew", pady=(0, 5))
        image_pane.add_widgets(self.create_image_controls)

        # 比例尺设置面板
        scale_pane = CollapsiblePane(scrollable_frame, text="比例尺设置", padding="5")
        scale_pane.grid(row=1, column=0, sticky="ew", pady=(0, 5))
        scale_pane.add_widgets(self.create_scale_controls)

        # 直径分级设置面板
        dia_pane = CollapsiblePane(scrollable_frame, text="直径分级设置", padding="5")
        dia_pane.grid(row=2, column=0, sticky="ew", pady=(0, 5))
        dia_pane.add_widgets(self.create_diameter_class_controls)

        # 过滤参数面板
        filter_pane = CollapsiblePane(scrollable_frame, text="过滤参数", padding="5")
        filter_pane.grid(row=3, column=0, sticky="ew", pady=(0, 5))
        filter_pane.add_widgets(self.create_filter_controls)

        # 批量处理面板
        batch_pane = CollapsiblePane(scrollable_frame, text="批量处理", padding="5")
        batch_pane.grid(row=4, column=0, sticky="ew", pady=(0, 5))
        batch_pane.add_widgets(self.create_batch_controls)

        # 输出设置面板
        output_pane = CollapsiblePane(scrollable_frame, text="输出设置", padding="5")
        output_pane.grid(row=5, column=0, sticky="ew", pady=(0, 5))
        output_pane.add_widgets(self.create_output_controls)

        # 操作按钮面板
        action_pane = ttk.LabelFrame(scrollable_frame, text="分析操作", padding="10")
        action_pane.grid(row=6, column=0, sticky="ew", pady=(0, 5))
        self.create_action_buttons(action_pane)

        # 创建样式
        style = ttk.Style()
        style.theme_use('clam')
        style.configure("Accent.TButton", foreground="white", background="#0078D7", font=("Arial", 9, "bold"))
        style.configure("Toggle.TButton", font=("Arial", 9, "bold"))
        style.configure("TLabelFrame", padding=5)
        style.configure("TLabel", padding=1)

        # 中间图像预览区域
        preview_frame = ttk.LabelFrame(main_frame, text="图像预览与操作", padding="5")
        preview_frame.grid(row=1, column=1, sticky=(tk.W, tk.E, tk.N, tk.S), padx=(0, 5))
        preview_frame.columnconfigure(0, weight=1)
        preview_frame.rowconfigure(0, weight=1)
        preview_frame.rowconfigure(1, weight=0)

        # 创建画布用于显示图像
        self.preview_canvas = tk.Canvas(preview_frame, bg="#2b2b2b", highlightthickness=1,
                                        highlightbackground="#555555")
        self.preview_canvas.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S), pady=(0, 5))

        # 添加滚动条
        self.h_scrollbar = ttk.Scrollbar(preview_frame, orient=tk.HORIZONTAL,
                                         command=self.preview_canvas.xview)
        self.h_scrollbar.grid(row=1, column=0, sticky=(tk.W, tk.E))
        self.v_scrollbar = ttk.Scrollbar(preview_frame, orient=tk.VERTICAL,
                                         command=self.preview_canvas.yview)
        self.v_scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))

        self.preview_canvas.configure(xscrollcommand=self.h_scrollbar.set,
                                      yscrollcommand=self.v_scrollbar.set)

        # 预览控制面板
        preview_control_frame = ttk.Frame(preview_frame)
        preview_control_frame.grid(row=2, column=0, columnspan=2, pady=(5, 0))

        # 图像类型选择
        self.image_type_var = tk.StringVar(value='原始图')
        preview_types = ['原始图', '增强图', '分割图', '过滤图', '根系计数', '结果图']

        type_frame = ttk.LabelFrame(preview_control_frame, text="显示类型", padding="5")
        type_frame.grid(row=0, column=0, padx=(0, 10))

        for i, preview_type in enumerate(preview_types):
            ttk.Radiobutton(
                type_frame,
                text=preview_type,
                variable=self.image_type_var,
                value=preview_type,
                command=lambda pt=preview_type: self.show_image(pt)
            ).grid(row=i // 3, column=i % 3, padx=2, pady=2)

        # 缩放控制
        zoom_frame = ttk.LabelFrame(preview_control_frame, text="缩放控制", padding="5")
        zoom_frame.grid(row=0, column=1)

        ttk.Button(zoom_frame, text="🔍-", command=self.zoom_out, width=4).grid(row=0, column=0, padx=2)
        ttk.Button(zoom_frame, text="🔍+", command=self.zoom_in, width=4).grid(row=0, column=1, padx=2)
        ttk.Button(zoom_frame, text="重置", command=self.zoom_reset, width=4).grid(row=0, column=2, padx=2)

        self.zoom_label_var = tk.StringVar(value="缩放: 100%")
        ttk.Label(zoom_frame, textvariable=self.zoom_label_var).grid(row=1, column=0, columnspan=3, pady=(5, 0))

        ttk.Button(zoom_frame, text="适应窗口", command=self.fit_to_window, width=12).grid(
            row=2, column=0, columnspan=3, pady=(5, 0)
        )

        # 右侧结果显示区域
        result_frame = ttk.LabelFrame(main_frame, text="分析结果", padding="5")
        result_frame.grid(row=1, column=2, sticky=(tk.W, tk.E, tk.N, tk.S))
        result_frame.columnconfigure(0, weight=1)
        result_frame.rowconfigure(0, weight=1)
        result_frame.rowconfigure(1, weight=0)

        # 创建文本区域显示结果
        self.result_text = scrolledtext.ScrolledText(result_frame, width=30, height=20,
                                                     font=("Courier New", 9))
        self.result_text.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

        # 结果操作按钮
        result_button_frame = ttk.Frame(result_frame)
        result_button_frame.grid(row=1, column=0, pady=(5, 0), sticky=tk.EW)

        ttk.Button(result_button_frame, text="显示详情", command=self.show_diameter_distribution, width=10).grid(
            row=0, column=0, padx=(0, 5)
        )
        ttk.Button(result_button_frame, text="复制结果", command=self.copy_results, width=10).grid(
            row=0, column=1
        )

        # 底部状态栏
        status_frame = ttk.Frame(main_frame)
        status_frame.grid(row=2, column=0, columnspan=3, pady=(5, 0), sticky=(tk.W, tk.E))

        # 进度条
        self.progress_var = tk.DoubleVar()
        self.progress_bar = ttk.Progressbar(status_frame, variable=self.progress_var, maximum=100)
        self.progress_bar.grid(row=0, column=0, sticky=(tk.W, tk.E), padx=(0, 10))
        status_frame.columnconfigure(0, weight=1)

        # 状态标签
        self.status_var = tk.StringVar(value="就绪")
        status_bar = ttk.Label(status_frame, textvariable=self.status_var, relief=tk.SUNKEN,
                               padding=(5, 3))
        status_bar.grid(row=0, column=1, sticky=(tk.W, tk.E))

        # 图像信息标签
        self.image_info_var = tk.StringVar(value="无图像")
        ttk.Label(status_frame, textvariable=self.image_info_var, padding=(5, 3)).grid(
            row=0, column=2, sticky=tk.E
        )

    def create_image_controls(self, parent):
        """创建图像操作控件"""
        # 图像路径
        ttk.Label(parent, text="图像路径:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.image_path_var = tk.StringVar()
        path_entry = ttk.Entry(parent, textvariable=self.image_path_var, width=25)
        path_entry.grid(row=1, column=0, sticky=tk.EW, pady=(0, 5))

        # 图像操作按钮
        btn_frame = ttk.Frame(parent)
        btn_frame.grid(row=2, column=0, sticky=tk.EW, pady=(0, 10))
        btn_frame.columnconfigure(0, weight=1)
        btn_frame.columnconfigure(1, weight=1)

        ttk.Button(btn_frame, text="选择图像", command=self.select_image).grid(
            row=0, column=0, padx=(0, 2), sticky=tk.EW
        )
        ttk.Button(btn_frame, text="预览", command=self.preview_image).grid(
            row=0, column=1, sticky=tk.EW
        )

        # 输出目录
        ttk.Label(parent, text="输出目录:").grid(row=3, column=0, sticky=tk.W, pady=(5, 5))
        self.output_path_var = tk.StringVar(value=os.path.expanduser("~/Desktop/根系分析结果"))
        output_entry = ttk.Entry(parent, textvariable=self.output_path_var, width=25)
        output_entry.grid(row=4, column=0, sticky=tk.EW, pady=(0, 5))

        ttk.Button(parent, text="选择目录", command=self.select_output_dir).grid(
            row=5, column=0, sticky=tk.EW, pady=(0, 5)
        )

    def create_scale_controls(self, parent):
        """创建比例尺设置控件"""
        # 测量设置
        ttk.Label(parent, text="通过测量设置:").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))

        meas_frame = ttk.Frame(parent)
        meas_frame.grid(row=1, column=0, sticky=tk.EW, pady=(0, 5))

        ttk.Label(meas_frame, text="长度(mm):").grid(row=0, column=0, sticky=tk.W)
        self.known_length_var = tk.DoubleVar(value=10.0)
        ttk.Spinbox(meas_frame, textvariable=self.known_length_var,
                    from_=0.1, to=1000.0, increment=0.1, width=8).grid(
            row=0, column=1, padx=(2, 5)
        )

        ttk.Label(meas_frame, text="像素:").grid(row=0, column=2)
        self.pixel_length_var = tk.IntVar(value=100)
        ttk.Spinbox(meas_frame, textvariable=self.pixel_length_var,
                    from_=1, to=10000, increment=1, width=8).grid(
            row=0, column=3, padx=(5, 0)
        )

        ttk.Button(parent, text="设置比例", command=self.set_scale_from_measurement, width=15).grid(
            row=2, column=0, sticky=tk.EW, pady=(0, 10)
        )

        # 图像尺寸设置
        ttk.Label(parent, text="通过图像尺寸设置:").grid(row=3, column=0, sticky=tk.W, pady=(0, 5))

        dim_frame = ttk.Frame(parent)
        dim_frame.grid(row=4, column=0, sticky=tk.EW, pady=(0, 5))

        ttk.Label(dim_frame, text="宽(mm):").grid(row=0, column=0, sticky=tk.W)
        self.image_width_mm_var = tk.DoubleVar(value=100.0)
        ttk.Spinbox(dim_frame, textvariable=self.image_width_mm_var,
                    from_=0.1, to=10000.0, increment=1.0, width=8).grid(
            row=0, column=1, padx=(2, 5)
        )

        ttk.Label(dim_frame, text="高(mm):").grid(row=0, column=2)
        self.image_height_mm_var = tk.DoubleVar(value=100.0)
        ttk.Spinbox(dim_frame, textvariable=self.image_height_mm_var,
                    from_=0.1, to=10000.0, increment=1.0, width=8).grid(
            row=0, column=3, padx=(5, 0)
        )

        ttk.Button(parent, text="设置尺寸", command=self.set_scale_from_dimensions, width=15).grid(
            row=5, column=0, sticky=tk.EW
        )

        # DPI转换
        ttk.Separator(parent, orient='horizontal').grid(row=6, column=0, sticky=tk.EW, pady=(10, 5))

        ttk.Label(parent, text="通过DPI设置:").grid(row=7, column=0, sticky=tk.W, pady=(0, 5))

        dpi_frame = ttk.Frame(parent)
        dpi_frame.grid(row=8, column=0, sticky=tk.EW, pady=(0, 5))

        ttk.Label(dpi_frame, text="DPI:").grid(row=0, column=0, sticky=tk.W)
        self.dpi_var = tk.IntVar(value=300)
        ttk.Spinbox(dpi_frame, textvariable=self.dpi_var,
                    from_=1, to=9600, increment=10, width=8).grid(
            row=0, column=1, padx=(5, 5)
        )
        ttk.Label(dpi_frame, text="(1 inch = 25.4 mm)").grid(row=0, column=2)

        ttk.Button(parent, text="DPI转换", command=self.set_scale_from_dpi, width=15).grid(
            row=9, column=0, sticky=tk.EW, pady=(0, 5)
        )

        # 参照物选取
        ttk.Separator(parent, orient='horizontal').grid(row=10, column=0, sticky=tk.EW, pady=(5, 5))

        self.ref_select_btn = ttk.Button(parent, text="选取参照物",
                                          command=self.toggle_ref_select_mode, width=15)
        self.ref_select_btn.grid(row=11, column=0, sticky=tk.EW, pady=(0, 5))
        self.ref_select_label = ttk.Label(parent, text="在图像上拖拽选取参照物，输入实际长度")
        self.ref_select_label.grid(row=12, column=0, sticky=tk.W, pady=(0, 5))

        # ROI框选
        ttk.Separator(parent, orient='horizontal').grid(row=13, column=0, sticky=tk.EW, pady=(5, 5))

        self.roi_btn = ttk.Button(parent, text="选取分析区域",
                                   command=self.toggle_roi_mode, width=15)
        self.roi_btn.grid(row=14, column=0, sticky=tk.EW, pady=(0, 5))
        self.clear_roi_btn = ttk.Button(parent, text="清除ROI",
                                         command=self.clear_roi, width=15)
        self.clear_roi_btn.grid(row=15, column=0, sticky=tk.EW, pady=(0, 5))

    def set_scale_from_dpi(self):
        """通过DPI设置比例尺"""
        try:
            dpi = self.dpi_var.get()
            if dpi <= 0:
                messagebox.showerror("错误", "DPI必须大于0")
                return
            pixel_to_mm = 25.4 / dpi
            self.analyzer.pixel_to_mm = pixel_to_mm
            self.param_vars['pixel_to_mm'].set(pixel_to_mm)
            self.update_status(f"DPI转换完成: {dpi} DPI → {pixel_to_mm:.4f} mm/像素")
            messagebox.showinfo("DPI转换", f"{dpi} DPI → {pixel_to_mm:.4f} mm/像素")
        except Exception as e:
            messagebox.showerror("错误", f"DPI转换失败: {str(e)}")

    def create_param_controls(self, parent):
        """创建分析参数控件"""
        # 像素转换系数
        ttk.Label(parent, text="像素转换系数(mm/像素):").grid(row=0, column=0, sticky=tk.W, pady=(0, 5))
        self.param_vars = {}
        self.param_vars['pixel_to_mm'] = tk.DoubleVar(value=0.1)
        ttk.Spinbox(parent, textvariable=self.param_vars['pixel_to_mm'],
                    from_=0.001, to=10.0, increment=0.001, width=12).grid(
            row=1, column=0, sticky=tk.W, pady=(0, 10)
        )

        # 分割方法
        ttk.Label(parent, text="分割方法:").grid(row=2, column=0, sticky=tk.W, pady=(0, 5))
        ttk.Label(parent, text="大津法 (固定)").grid(row=3, column=0, sticky=tk.W, pady=(0, 10))

        # 根系计数参数
        ttk.Label(parent, text="最小根系大小(像素):").grid(row=4, column=0, sticky=tk.W, pady=(0, 5))
        self.min_root_size_var = tk.IntVar(value=20)
        ttk.Spinbox(parent, textvariable=self.min_root_size_var,
                    from_=10, to=1000, increment=10, width=12).grid(
            row=5, column=0, sticky=tk.W
        )

    def create_filter_controls(self, parent):
        """创建过滤参数控件"""
        # 过滤参数说明
        ttk.Label(parent, text="过滤参数（仅保留三个关键参数）", font=("Arial", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, pady=(0, 10)
        )

        # 过滤参数网格
        filter_param_grid = [
            ("最小根长(像素):", "min_length", 5, 1, 500, 1),
            ("最小根面积(像素):", "min_area", 20, 1, 1000, 1),
            ("最小纵横比:", "min_aspect_ratio", 1.0, 0.1, 20.0, 0.1),
        ]

        for i, (label_text, param_name, default_val, from_val, to_val, increment) in enumerate(filter_param_grid, 1):
            ttk.Label(parent, text=label_text).grid(row=i, column=0, sticky=tk.W, pady=(0, 2))

            if isinstance(default_val, float):
                var = tk.DoubleVar(value=default_val)
            else:
                var = tk.IntVar(value=default_val)

            ttk.Spinbox(
                parent,
                textvariable=var,
                from_=from_val,
                to=to_val,
                increment=increment,
                width=12
            ).grid(row=i, column=1, pady=(0, 2), padx=(5, 0), sticky=tk.W)

            self.param_vars[param_name] = var

    def create_output_controls(self, parent):
        """创建输出设置控件"""
        ttk.Label(parent, text="分析后自动生成的输出:", font=("Arial", 9, "bold")).grid(
            row=0, column=0, sticky=tk.W, pady=(0, 8)
        )
        ttk.Checkbutton(parent, text="保存CSV数据", variable=self.save_csv_var).grid(
            row=1, column=0, sticky=tk.W, pady=(0, 2)
        )
        ttk.Checkbutton(parent, text="保存JSON数据", variable=self.save_json_var).grid(
            row=2, column=0, sticky=tk.W, pady=(0, 2)
        )
        ttk.Checkbutton(parent, text="生成叠加图像", variable=self.save_overlay_var).grid(
            row=3, column=0, sticky=tk.W, pady=(0, 2)
        )
        ttk.Checkbutton(parent, text="生成详细报告图", variable=self.save_report_var).grid(
            row=4, column=0, sticky=tk.W, pady=(0, 2)
        )
        ttk.Checkbutton(parent, text="图像中显示比例尺", variable=self.show_scale_var).grid(
            row=5, column=0, sticky=tk.W
        )

    def create_diameter_class_controls(self, parent):
        """创建直径分级自定义控件"""
        ttk.Label(parent, text="自定义根系直径分级标准",
                  font=("Arial", 9, "bold")).grid(row=0, column=0, columnspan=3,
                                                   sticky=tk.W, pady=(0, 5))

        # Treeview 显示当前分级
        columns = ('name', 'min_d', 'max_d')
        self.dia_tree = ttk.Treeview(parent, columns=columns, show='headings', height=6)
        self.dia_tree.heading('name', text='分级名称')
        self.dia_tree.heading('min_d', text='最小直径(mm)')
        self.dia_tree.heading('max_d', text='最大直径(mm)')
        self.dia_tree.column('name', width=80, anchor='center')
        self.dia_tree.column('min_d', width=85, anchor='center')
        self.dia_tree.column('max_d', width=85, anchor='center')
        self.dia_tree.grid(row=1, column=0, columnspan=3, sticky=tk.EW, pady=(0, 5))
        self._refresh_dia_tree()

        # 按钮
        btn_frame = ttk.Frame(parent)
        btn_frame.grid(row=2, column=0, columnspan=3, sticky=tk.EW)
        ttk.Button(btn_frame, text="添加", command=self._dia_add_class, width=8).pack(
            side=tk.LEFT, padx=(0, 2))
        ttk.Button(btn_frame, text="编辑", command=self._dia_edit_class, width=8).pack(
            side=tk.LEFT, padx=(0, 2))
        ttk.Button(btn_frame, text="删除", command=self._dia_delete_class, width=8).pack(
            side=tk.LEFT, padx=(0, 2))
        ttk.Button(btn_frame, text="恢复默认", command=self._dia_reset_classes, width=8).pack(
            side=tk.LEFT)

    def _refresh_dia_tree(self):
        """刷新直径分级树形视图"""
        for item in self.dia_tree.get_children():
            self.dia_tree.delete(item)
        for name, min_val, max_val in self.diameter_classes:
            max_display = '无穷' if max_val == float('inf') else f'{max_val:.1f}'
            self.dia_tree.insert('', tk.END, values=(name, f'{min_val:.1f}', max_display))

    def _dia_get_selected_index(self):
        """返回选中分级的索引和名称，若无选中返回 None"""
        selection = self.dia_tree.selection()
        if not selection:
            return None
        item = self.dia_tree.item(selection[0])
        name = item['values'][0]
        for i, (n, _, _) in enumerate(self.diameter_classes):
            if n == name:
                return i
        return None

    def _dia_class_dialog(self, title, name='', min_val='', max_val=''):
        """添加/编辑分级对话框，返回 (name, min_val, max_val) 或 None"""
        dialog = tk.Toplevel(self.root)
        dialog.title(title)
        dialog.geometry('300x200')
        dialog.transient(self.root)
        dialog.grab_set()
        dialog.resizable(False, False)

        frame = ttk.Frame(dialog, padding=15)
        frame.pack(fill=tk.BOTH, expand=True)

        ttk.Label(frame, text='分级名称:').grid(row=0, column=0, sticky=tk.W, pady=(0, 8))
        name_var = tk.StringVar(value=name)
        ttk.Entry(frame, textvariable=name_var, width=20).grid(row=0, column=1, pady=(0, 8), padx=(10, 0))

        ttk.Label(frame, text='最小直径(mm):').grid(row=1, column=0, sticky=tk.W, pady=(0, 8))
        min_var = tk.StringVar(value=str(min_val))
        ttk.Entry(frame, textvariable=min_var, width=20).grid(row=1, column=1, pady=(0, 8), padx=(10, 0))

        ttk.Label(frame, text='最大直径(mm):').grid(row=2, column=0, sticky=tk.W, pady=(0, 12))
        max_var = tk.StringVar(value=str(max_val))
        ttk.Entry(frame, textvariable=max_var, width=20).grid(row=2, column=1, pady=(0, 12), padx=(10, 0))
        ttk.Label(frame, text='(留空表示无上限)', font=('Arial', 7)).grid(
            row=3, column=1, sticky=tk.W)

        result = {'name': None, 'min_val': None, 'max_val': None}

        def on_ok():
            n = name_var.get().strip()
            if not n:
                messagebox.showwarning('警告', '名称不能为空', parent=dialog)
                return
            try:
                mn = float(min_var.get())
                mx_str = max_var.get().strip()
                mx = float('inf') if mx_str == '' else float(mx_str)
            except ValueError:
                messagebox.showwarning('警告', '直径值必须为有效数字', parent=dialog)
                return
            if mn < 0 or (mx != float('inf') and mx < 0):
                messagebox.showwarning('警告', '直径值不能为负', parent=dialog)
                return
            if mx != float('inf') and mn >= mx:
                messagebox.showwarning('警告', '最小直径必须小于最大直径', parent=dialog)
                return
            result['name'] = n
            result['min_val'] = mn
            result['max_val'] = mx
            dialog.destroy()

        btn_frame = ttk.Frame(frame)
        btn_frame.grid(row=4, column=0, columnspan=2, pady=(10, 0))
        ttk.Button(btn_frame, text='确定', command=on_ok, width=10).pack(side=tk.LEFT, padx=(0, 10))
        ttk.Button(btn_frame, text='取消', command=dialog.destroy, width=10).pack(side=tk.LEFT)

        dialog.wait_window()
        if result['name'] is not None:
            return result['name'], result['min_val'], result['max_val']
        return None

    def _dia_add_class(self):
        """添加新分级"""
        # 建议范围：取当前最大有限上限为起点
        max_upper = 5.0
        for _, _, mx in self.diameter_classes:
            if mx != float('inf') and mx > max_upper:
                max_upper = mx
        new_min = max_upper
        new_max = new_min * 2
        result = self._dia_class_dialog('添加直径分级', min_val=new_min, max_val=new_max)
        if result:
            self.diameter_classes.append(result)
            self._refresh_dia_tree()

    def _dia_edit_class(self):
        """编辑选中分级"""
        idx = self._dia_get_selected_index()
        if idx is None:
            return
        name, min_val, max_val = self.diameter_classes[idx]
        max_str = '' if max_val == float('inf') else max_val
        result = self._dia_class_dialog('编辑直径分级', name=name, min_val=min_val, max_val=max_str)
        if result:
            self.diameter_classes[idx] = result
            self._refresh_dia_tree()

    def _dia_delete_class(self):
        """删除选中分级"""
        idx = self._dia_get_selected_index()
        if idx is None:
            return
        if len(self.diameter_classes) <= 2:
            messagebox.showwarning('警告', '至少需要保留2个分级')
            return
        del self.diameter_classes[idx]
        self._refresh_dia_tree()

    def _dia_reset_classes(self):
        """恢复默认分级"""
        if messagebox.askyesno('确认', '确定要恢复为默认直径分级标准吗？'):
            self.diameter_classes = list(RootSystemAnalyzer.DEFAULT_DIAMETER_CLASSES)
            self._refresh_dia_tree()

    def create_batch_controls(self, parent):
        """创建批量处理控件"""
        # 批量文件列表
        ttk.Label(parent, text="批量文件列表:").grid(row=0, column=0, columnspan=2, sticky=tk.W, pady=(0, 5))

        # 创建列表框
        batch_frame = ttk.Frame(parent)
        batch_frame.grid(row=1, column=0, columnspan=2, pady=(0, 5), sticky=tk.EW)

        self.batch_listbox = tk.Listbox(batch_frame, height=4, font=("Courier New", 8))
        self.batch_listbox.grid(row=0, column=0, sticky=(tk.W, tk.E, tk.N, tk.S))

        # 添加滚动条
        scrollbar = ttk.Scrollbar(batch_frame, orient=tk.VERTICAL, command=self.batch_listbox.yview)
        scrollbar.grid(row=0, column=1, sticky=(tk.N, tk.S))
        self.batch_listbox.configure(yscrollcommand=scrollbar.set)

        # 批量操作按钮
        batch_btn_frame = ttk.Frame(parent)
        batch_btn_frame.grid(row=2, column=0, columnspan=2, pady=(0, 10), sticky=tk.EW)
        batch_btn_frame.columnconfigure(0, weight=1)
        batch_btn_frame.columnconfigure(1, weight=1)

        ttk.Button(batch_btn_frame, text="清空列表", command=self.clear_batch_list).grid(
            row=0, column=0, padx=(0, 2), sticky=tk.EW
        )
        ttk.Button(batch_btn_frame, text="批量选择", command=self.select_images_batch).grid(
            row=0, column=1, sticky=tk.EW
        )

        # 并行处理设置
        ttk.Label(parent, text="并行处理设置:", font=("Arial", 9, "bold")).grid(
            row=3, column=0, columnspan=2, sticky=tk.W, pady=(5, 5)
        )

        ttk.Label(parent, text="最大并发进程:").grid(row=4, column=0, sticky=tk.W, pady=(0, 2))
        self.max_workers_var = tk.IntVar(value=5)
        ttk.Label(parent, text="5 (固定)").grid(
            row=4, column=1, sticky=tk.W, pady=(0, 2), padx=(5, 0)
        )

        ttk.Label(parent, text="超时时间(秒):").grid(row=5, column=0, sticky=tk.W, pady=(0, 2))
        self.batch_timeout_var = tk.IntVar(value=self.batch_timeout)
        ttk.Spinbox(parent, textvariable=self.batch_timeout_var,
                    from_=60, to=3600, increment=30, width=12).grid(
            row=5, column=1, sticky=tk.W, pady=(0, 2), padx=(5, 0)
        )

        # 批量分析按钮
        ttk.Button(parent, text="批量分析", command=self.batch_analysis, width=15).grid(
            row=6, column=0, sticky=tk.EW, pady=(5, 2)
        )
        ttk.Button(parent, text="并行批量分析", command=self.parallel_batch_analysis,
                   style="Accent.TButton", width=15).grid(
            row=6, column=1, sticky=tk.EW, pady=(5, 2), padx=(5, 0)
        )

    def create_action_buttons(self, parent):
        """创建操作按钮"""
        # 主要操作按钮
        ttk.Button(parent, text="开始分析", command=self.start_analysis,
                   style="Accent.TButton", width=20).grid(
            row=0, column=0, pady=(0, 10), sticky=tk.EW
        )

        # 辅助功能按钮
        aux_btn_frame = ttk.Frame(parent)
        aux_btn_frame.grid(row=1, column=0, sticky=tk.EW, pady=(0, 10))
        aux_btn_frame.columnconfigure(0, weight=1)
        aux_btn_frame.columnconfigure(1, weight=1)

        ttk.Button(aux_btn_frame, text="导出结果图", command=self.export_result_image).grid(
            row=0, column=0, padx=(0, 2), sticky=tk.EW
        )
        ttk.Button(aux_btn_frame, text="导出数据", command=self.export_results).grid(
            row=0, column=1, sticky=tk.EW
        )

        # 退出按钮
        ttk.Button(parent, text="退出程序", command=self.root.quit, width=20).grid(
            row=2, column=0, pady=(10, 0), sticky=tk.EW
        )

    def toggle_scan_optimization(self):
        """切换扫描图像优化状态"""
        self.scan_optimization_enabled = self.scan_optimization_var.get()
        self.scan_background_type = self.scan_background_type_var.get()
        self.scan_quality = self.scan_quality_var.get()

        # 更新分析器设置
        if hasattr(self.analyzer, 'enable_scan_optimization'):
            self.analyzer.enable_scan_optimization(self.scan_optimization_enabled)
            self.analyzer.set_scan_background_type(self.scan_background_type)
            self.analyzer.set_scan_quality(self.scan_quality)

            # 如果已加载图像，重新增强图像
            if hasattr(self.analyzer, 'gray_image'):
                # 重新显示增强图像
                self.show_image('增强图')
                self.update_status(f"扫描图像优化{'已启用' if self.scan_optimization_enabled else '已禁用'}")

    def bind_events(self):
        """绑定鼠标事件"""
        # 鼠标滚轮缩放
        self.preview_canvas.bind("<MouseWheel>", self.on_mousewheel)  # Windows
        self.preview_canvas.bind("<Button-4>", self.on_mousewheel)  # Linux scroll up
        self.preview_canvas.bind("<Button-5>", self.on_mousewheel)  # Linux scroll down

        # 鼠标拖拽
        self.preview_canvas.bind("<ButtonPress-1>", self.start_pan)
        self.preview_canvas.bind("<B1-Motion>", self.do_pan)
        self.preview_canvas.bind("<ButtonRelease-1>", self.stop_pan)

        # 适应窗口大小变化
        self.preview_canvas.bind("<Configure>", self.on_canvas_configure)

    def on_mousewheel(self, event):
        """鼠标滚轮缩放"""
        if event.num == 5 or event.delta < 0:
            self.zoom_out()
        elif event.num == 4 or event.delta > 0:
            self.zoom_in()
        return "break"

    def start_pan(self, event):
        """开始拖拽/参照物选取/ROI框选"""
        if self.ref_select_mode:
            self.ref_start_point = (self.preview_canvas.canvasx(event.x),
                                     self.preview_canvas.canvasy(event.y))
            self.panning = False
        elif self.roi_select_mode:
            self.roi_start = (self.preview_canvas.canvasx(event.x),
                               self.preview_canvas.canvasy(event.y))
            self.panning = False
        else:
            self.preview_canvas.scan_mark(event.x, event.y)
            self.panning = True

    def do_pan(self, event):
        """执行拖拽/参照物画线/ROI框选"""
        if self.ref_select_mode and self.ref_start_point is not None:
            x1, y1 = self.ref_start_point
            x2 = self.preview_canvas.canvasx(event.x)
            y2 = self.preview_canvas.canvasy(event.y)
            if self.ref_line_id:
                self.preview_canvas.delete(self.ref_line_id)
            self.ref_line_id = self.preview_canvas.create_line(
                x1, y1, x2, y2,
                fill="#FFD700", width=3, dash=(5, 3), tags="ref_line"
            )
            r = 4
            self.preview_canvas.delete("ref_point")
            self.preview_canvas.create_oval(x1 - r, y1 - r, x1 + r, y1 + r,
                                             fill="#00FF00", outline="white", tags="ref_point")
            self.preview_canvas.create_oval(x2 - r, y2 - r, x2 + r, y2 + r,
                                             fill="#FF4444", outline="white", tags="ref_point")
        elif self.roi_select_mode and self.roi_start is not None:
            x1, y1 = self.roi_start
            x2 = self.preview_canvas.canvasx(event.x)
            y2 = self.preview_canvas.canvasy(event.y)
            if self.roi_rect_id:
                self.preview_canvas.delete(self.roi_rect_id)
            self.roi_rect_id = self.preview_canvas.create_rectangle(
                x1, y1, x2, y2,
                outline="#00BFFF", width=2, dash=(6, 3),
                stipple="gray25", tags="roi_rect"
            )
        elif self.panning:
            self.preview_canvas.scan_dragto(event.x, event.y, gain=1)

    def stop_pan(self, event):
        """停止拖拽/完成参照物选取/完成ROI框选"""
        if self.ref_select_mode and self.ref_start_point is not None:
            x2 = self.preview_canvas.canvasx(event.x)
            y2 = self.preview_canvas.canvasy(event.y)
            self.ref_end_point = (x2, y2)
            self._finish_ref_select()
        elif self.roi_select_mode and self.roi_start is not None:
            x2 = self.preview_canvas.canvasx(event.x)
            y2 = self.preview_canvas.canvasy(event.y)
            self.roi_end = (x2, y2)
            self._finish_roi_select()
        else:
            self.panning = False

    def _finish_ref_select(self):
        """完成参照物选取，弹出对话框设置比例尺"""
        if self.ref_start_point is None or self.ref_end_point is None:
            return
        x1, y1 = self.ref_start_point
        x2, y2 = self.ref_end_point

        # 计算像素距离（转换为图像坐标）
        pixel_dist = math.sqrt((x2 - x1) ** 2 + (y2 - y1) ** 2)
        pixel_dist_image = pixel_dist / self.zoom_level

        # 弹出对话框
        result = simpledialog.askfloat(
            "参照物长度",
            f"选取的线段像素长度: {pixel_dist_image:.1f} px\n\n"
            "请输入该参照物的实际长度 (mm):",
            parent=self.root,
            minvalue=0.001
        )

        if result is not None and result > 0:
            self.analyzer.pixel_to_mm = result / pixel_dist_image
            self.param_vars['pixel_to_mm'].set(self.analyzer.pixel_to_mm)
            self.update_status(
                f"参照物比例尺: {result:.2f} mm / {pixel_dist_image:.0f} px = "
                f"{self.analyzer.pixel_to_mm:.4f} mm/像素"
            )
            messagebox.showinfo("比例尺设置成功",
                f"实际长度: {result:.2f} mm\n"
                f"像素长度: {pixel_dist_image:.0f} px\n"
                f"转换系数: {self.analyzer.pixel_to_mm:.4f} mm/像素"
            )

        # 退出选取模式
        self.toggle_ref_select_mode()

    def toggle_ref_select_mode(self):
        """切换参照物选取模式"""
        if not hasattr(self.analyzer, 'original_image'):
            messagebox.showwarning("警告", "请先加载图像")
            return

        self.ref_select_mode = not self.ref_select_mode

        if self.ref_select_mode:
            self.ref_select_btn.configure(text="取消选取")
            self.preview_canvas.configure(cursor="crosshair")
            self.ref_start_point = None
            self.ref_end_point = None
            self.ref_line_id = None
            self.update_status("参照物选取模式: 在图像上拖拽以选取参照物")
        else:
            self.ref_select_btn.configure(text="选取参照物")
            self.preview_canvas.configure(cursor="")
            self.preview_canvas.delete("ref_line")
            self.preview_canvas.delete("ref_point")
            self.ref_start_point = None
            self.ref_end_point = None
            self.ref_line_id = None
            self.update_status("已退出参照物选取模式")

    def _finish_roi_select(self):
        """完成ROI框选"""
        if self.roi_start is None or self.roi_end is None:
            return
        x1, y1 = self.roi_start
        x2, y2 = self.roi_end
        # 标准化坐标
        x1, x2 = min(x1, x2), max(x1, x2)
        y1, y2 = min(y1, y2), max(y1, y2)

        min_size = 10
        if abs(x2 - x1) < min_size or abs(y2 - y1) < min_size:
            self.preview_canvas.delete("roi_rect")
            self.roi_start = None
            self.roi_end = None
            self.roi_rect_id = None
            self.preview_canvas.delete("roi_display")
            messagebox.showwarning("警告", "选取区域太小，请重新框选")
            return

        # 转换为图像坐标存储（与缩放无关）
        self.roi_active = (x1 / self.zoom_level, y1 / self.zoom_level,
                           x2 / self.zoom_level, y2 / self.zoom_level)
        self._draw_roi_display()
        img_x1, img_y1, img_x2, img_y2 = self.roi_active
        self.update_status(f"ROI已设置: ({img_x1:.0f},{img_y1:.0f})-({img_x2:.0f},{img_y2:.0f})")
        self.toggle_roi_mode()

    def _draw_roi_display(self):
        """在画布上绘制活跃的ROI框（图像坐标→画布坐标）"""
        self.preview_canvas.delete("roi_display")
        if self.roi_active:
            z = self.zoom_level
            x1, y1, x2, y2 = [v * z for v in self.roi_active]
            self.preview_canvas.create_rectangle(
                x1, y1, x2, y2,
                outline="#00BFFF", width=2, dash=(6, 3),
                stipple="gray25", tags="roi_display"
            )

    def toggle_roi_mode(self):
        """切换ROI框选模式"""
        if not hasattr(self.analyzer, 'original_image'):
            messagebox.showwarning("警告", "请先加载图像")
            return

        if self.ref_select_mode:
            self.toggle_ref_select_mode()

        self.roi_select_mode = not self.roi_select_mode

        if self.roi_select_mode:
            self.roi_btn.configure(text="取消框选")
            self.preview_canvas.configure(cursor="crosshair")
            self.roi_start = None
            self.roi_end = None
            self.roi_rect_id = None
            self.preview_canvas.delete("roi_rect")
            self.update_status("ROI框选模式: 在图像上拖拽矩形框选取分析区域")
        else:
            self.roi_btn.configure(text="选取分析区域")
            self.preview_canvas.configure(cursor="")
            self.preview_canvas.delete("roi_rect")
            self.roi_start = None
            self.roi_end = None
            self.roi_rect_id = None
            self.update_status("已退出ROI框选模式")

    def clear_roi(self):
        """清除ROI"""
        self.roi_active = None
        self.preview_canvas.delete("roi_display")
        self.update_status("ROI已清除，恢复全图分析")

    def on_canvas_configure(self, event):
        """画布大小变化时更新"""
        self.update_scrollregion()

    def update_scrollregion(self):
        """更新滚动区域"""
        self.preview_canvas.configure(scrollregion=self.preview_canvas.bbox("all"))

    def zoom_in(self):
        """放大图像"""
        if self.zoom_level < self.max_zoom:
            self.zoom_level += self.zoom_step
            self.update_zoom()
            self.refresh_displayed_image()

    def zoom_out(self):
        """缩小图像"""
        if self.zoom_level > self.min_zoom:
            self.zoom_level -= self.zoom_step
            self.update_zoom()
            self.refresh_displayed_image()

    def zoom_reset(self):
        """重置缩放"""
        self.zoom_level = 1.0
        self.pan_x = 0
        self.pan_y = 0
        self.update_zoom()
        self.refresh_displayed_image()
        self.preview_canvas.xview_moveto(0)
        self.preview_canvas.yview_moveto(0)

    def fit_to_window(self):
        """适应窗口大小"""
        if not hasattr(self.analyzer, 'original_image'):
            return

        # 获取画布尺寸
        canvas_width = self.preview_canvas.winfo_width()
        canvas_height = self.preview_canvas.winfo_height()

        if canvas_width <= 1 or canvas_height <= 1:
            return

        # 获取图像尺寸
        img_height, img_width = self.analyzer.original_image.shape[:2]

        # 计算合适的缩放比例
        scale_x = canvas_width / img_width * 0.9
        scale_y = canvas_height / img_height * 0.9
        scale = min(scale_x, scale_y)

        self.zoom_level = scale
        self.update_zoom()
        self.refresh_displayed_image()
        self.preview_canvas.xview_moveto(0)
        self.preview_canvas.yview_moveto(0)

    def update_zoom(self):
        """更新缩放标签"""
        zoom_percent = int(self.zoom_level * 100)
        self.zoom_label_var.set(f"缩放: {zoom_percent}%")

    def refresh_displayed_image(self):
        """刷新显示的图像"""
        self.show_image(self.current_image_type)

    def select_image(self):
        """选择单个图像文件"""
        filetypes = [
            ('图像文件', '*.jpg *.jpeg *.png *.bmp *.tiff *.tif'),
            ('所有文件', '*.*')
        ]

        initial_dir = os.path.dirname(self.image_path_var.get()) if self.image_path_var.get() else None

        filepath = filedialog.askopenfilename(
            title="选择根系图像",
            filetypes=filetypes,
            initialdir=initial_dir
        )

        if filepath:
            self.image_path_var.set(filepath)
            self.current_image_path = filepath
            self.zoom_reset()
            self.preview_image()

    def select_images_batch(self):
        """选择多个图像文件"""
        filetypes = [
            ('图像文件', '*.jpg *.jpeg *.png *.bmp *.tiff *.tif'),
            ('所有文件', '*.*')
        ]

        initial_dir = None
        if self.image_path_var.get():
            initial_dir = os.path.dirname(self.image_path_var.get())

        filepaths = filedialog.askopenfilenames(
            title="选择多个根系图像",
            filetypes=filetypes,
            initialdir=initial_dir
        )

        if filepaths:
            # 保存到列表 - 确保是列表而不是元组
            self.batch_files = list(filepaths)
            # 显示第一个文件路径
            if self.batch_files:
                self.image_path_var.set(self.batch_files[0])
            self.update_status(f"已选择 {len(filepaths)} 个图像文件")

            # 更新批量文件列表显示
            if hasattr(self, 'batch_listbox'):
                self.batch_listbox.delete(0, tk.END)
                for filepath in self.batch_files:
                    self.batch_listbox.insert(tk.END, os.path.basename(filepath))

    def clear_batch_list(self):
        """清空批量文件列表"""
        self.batch_files = []
        if hasattr(self, 'batch_listbox'):
            self.batch_listbox.delete(0, tk.END)
        self.image_path_var.set("")
        self.update_status("已清空批量文件列表")

    def select_output_dir(self):
        """选择输出目录"""
        initial_dir = self.output_path_var.get() if self.output_path_var.get() else None

        dirpath = filedialog.askdirectory(
            title="选择结果输出目录",
            initialdir=initial_dir
        )

        if dirpath:
            self.output_path_var.set(dirpath)
            self.output_dir = dirpath

    def set_scale_from_measurement(self):
        """通过测量设置比例尺"""
        try:
            measured_length = self.known_length_var.get()
            pixel_length = self.pixel_length_var.get()

            success, message = self.analyzer.set_scale_from_measurement(measured_length, pixel_length)
            if success:
                self.param_vars['pixel_to_mm'].set(self.analyzer.pixel_to_mm)
                self.update_status(message)
                messagebox.showinfo("成功", message)
            else:
                messagebox.showerror("错误", message)
        except Exception as e:
            messagebox.showerror("错误", f"设置比例失败: {str(e)}")

    def set_scale_from_dimensions(self):
        """通过图像尺寸设置比例尺"""
        try:
            if not hasattr(self.analyzer, 'original_image'):
                messagebox.showwarning("警告", "请先加载图像")
                return

            width_mm = self.image_width_mm_var.get()
            height_mm = self.image_height_mm_var.get()

            success, message = self.analyzer.set_scale_from_dimensions(width_mm, height_mm)
            if success:
                self.param_vars['pixel_to_mm'].set(self.analyzer.pixel_to_mm)
                self.update_status(message)
                messagebox.showinfo("成功", message)
            else:
                messagebox.showerror("错误", message)
        except Exception as e:
            messagebox.showerror("错误", f"设置比例失败: {str(e)}")

    def preview_image(self):
        """预览图像"""
        filepath = self.image_path_var.get()
        if not filepath or not os.path.exists(filepath):
            messagebox.showwarning("警告", "请先选择有效的图像文件")
            return

        try:
            # 更新扫描优化设置
            self.toggle_scan_optimization()

            # 加载图像
            success, message = self.analyzer.load_image(filepath)
            if not success:
                messagebox.showerror("错误", message)
                return

            # 更新图像信息
            if hasattr(self.analyzer, 'image_width'):
                info_text = f"{self.analyzer.image_width}×{self.analyzer.image_height} 像素"
                if self.scan_optimization_enabled:
                    info_text += " [扫描优化]"
                self.image_info_var.set(info_text)

            # 更新预览
            self.zoom_reset()
            self.fit_to_window()
            self.show_image('原始图')

            # 显示扫描图像检测结果
            if self.scan_optimization_enabled and self.analyzer.scan_params['is_scanned']:
                scan_info = f"检测到扫描图像: 背景={self.analyzer.scan_params['background_type']}, 质量={self.analyzer.scan_params['scan_quality']}"
                self.update_status(f"{message} - {scan_info}")
            else:
                self.update_status(message)

        except Exception as e:
            messagebox.showerror("错误", f"预览失败: {str(e)}")

    def show_image(self, image_type='原始图'):
        """显示指定类型的图像"""
        self.current_image_type = image_type

        if not hasattr(self.analyzer, 'original_image'):
            return

        try:
            # 清除画布上的旧图像和标题（保留参照物选取元素）
            self.preview_canvas.delete("display")

            # 根据类型选择图像
            if image_type == '原始图':
                img = cv2.cvtColor(self.analyzer.original_image, cv2.COLOR_BGR2RGB)
                title = "原始图像"
            elif image_type == '增强图':
                if self.scan_optimization_enabled and hasattr(self.analyzer, 'scan_enhanced'):
                    img = cv2.cvtColor(self.analyzer.scan_enhanced, cv2.COLOR_GRAY2RGB)
                    title = "扫描图像增强"
                elif hasattr(self.analyzer, 'enhanced_image'):
                    img = cv2.cvtColor(self.analyzer.enhanced_image, cv2.COLOR_GRAY2RGB)
                    title = "增强图像"
                else:
                    img = cv2.cvtColor(self.analyzer.original_image, cv2.COLOR_BGR2RGB)
                    title = "原始图像"
            elif image_type == '分割图' and hasattr(self.analyzer, 'binary_mask'):
                img = cv2.cvtColor(self.analyzer.binary_mask, cv2.COLOR_GRAY2RGB)
                title = "扫描图像分割" if self.scan_optimization_enabled else "分割结果（大津法）"
            elif image_type == '过滤图' and hasattr(self.analyzer, 'filtered_mask'):
                img = cv2.cvtColor(self.analyzer.filtered_mask, cv2.COLOR_GRAY2RGB)
                title = f"扫描图像过滤 ({self.analyzer.filtered_count}个)" if self.scan_optimization_enabled else f"过滤后根系 ({self.analyzer.filtered_count}个)"
            elif image_type == '根系计数' and hasattr(self.analyzer, 'color_map'):
                img = self.analyzer.color_map
                title = f"根系计数 ({getattr(self.analyzer, 'root_count', 0)}个)"
            elif image_type == '结果图' and hasattr(self.analyzer, 'filtered_mask'):
                overlay = self.analyzer.original_image.copy()
                overlay[self.analyzer.filtered_mask > 0] = [0, 255, 0]
                img = cv2.cvtColor(overlay, cv2.COLOR_BGR2RGB)
                title = "检测结果叠加"
            else:
                img = cv2.cvtColor(self.analyzer.original_image, cv2.COLOR_BGR2RGB)
                title = "原始图像"

            # 调整图像大小
            height, width = img.shape[:2]
            new_width = int(width * self.zoom_level)
            new_height = int(height * self.zoom_level)

            img_resized = cv2.resize(img, (new_width, new_height))

            # 转换为PIL图像并直接在Canvas上绘制
            img_pil = Image.fromarray(img_resized)
            img_tk = ImageTk.PhotoImage(img_pil)
            self._img_tk_ref = img_tk  # 保持引用防止GC

            self.preview_canvas.create_image(0, 0, image=img_tk, anchor="nw", tags="display")

            # 标题文字
            self.preview_canvas.create_text(10, new_height + 5, text=title,
                                             anchor="nw", fill="white",
                                             font=("Arial", 9, "bold"),
                                             tags="display")

            # 更新滚动区域
            self.preview_canvas.configure(scrollregion=(0, 0, new_width, new_height + 25))

            # 更新按钮状态
            self.image_type_var.set(image_type)

            # 绘制当前ROI框
            self._draw_roi_display()

        except Exception as e:
            print(f"显示图像失败: {e}")

    def count_roots(self):
        """计数根系"""
        if not hasattr(self.analyzer, 'filtered_mask') or np.sum(self.analyzer.filtered_mask) == 0:
            messagebox.showwarning("警告", "请先进行分析，获取根系掩码")
            return

        try:
            min_size = self.min_root_size_var.get()
            success, message = self.analyzer.count_roots(min_size=min_size)

            if success:
                self.update_status(message)
                messagebox.showinfo("成功", message)

                # 更新结果显示
                if hasattr(self.analyzer, 'root_count'):
                    # 重新计算参数以包含计数结果
                    self.analyzer.calculate_parameters()
                    self.display_results(self.analyzer.results)

                    # 显示根系计数图像
                    self.show_image('根系计数')
            else:
                messagebox.showerror("错误", message)
        except Exception as e:
            messagebox.showerror("错误", f"根系计数失败: {str(e)}")

    def calculate_parameters(self):
        """计算根系参数"""
        if not hasattr(self.analyzer, 'connected_components') or not self.analyzer.connected_components:
            messagebox.showwarning("警告", "请先进行根系计数")
            return

        try:
            success, message = self.analyzer.calculate_root_parameters()

            if success:
                # 重新计算所有参数
                self.analyzer.calculate_parameters()
                self.display_results(self.analyzer.results)

                self.update_status(message)
                messagebox.showinfo("成功", message)
            else:
                messagebox.showerror("错误", message)
        except Exception as e:
            messagebox.showerror("错误", f"参数计算失败: {str(e)}")

    def show_diameter_distribution(self):
        """显示根系直径分级详情"""
        if not hasattr(self.analyzer, 'root_parameters') or not self.analyzer.root_parameters.get(
                'diameter_distribution'):
            messagebox.showinfo("信息", "没有直径分级数据")
            return

        # 创建详细窗口
        detail_window = tk.Toplevel(self.root)
        detail_window.title("根系直径分级详情")
        detail_window.geometry("800x600")

        # 创建文本区域
        text_area = scrolledtext.ScrolledText(detail_window, width=80, height=30,
                                              font=("Courier New", 9))
        text_area.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # 添加标题
        text_area.insert(tk.END, "=" * 70 + "\n")
        text_area.insert(tk.END, "根系直径分级详情\n")
        text_area.insert(tk.END, "=" * 70 + "\n\n")

        # 添加扫描优化信息
        if self.scan_optimization_enabled:
            text_area.insert(tk.END, "扫描图像优化: 已启用\n")
            text_area.insert(tk.END, f"背景类型: {self.analyzer.scan_params['background_type']}\n")
            text_area.insert(tk.END, f"扫描质量: {self.analyzer.scan_params['scan_quality']}\n")
            text_area.insert(tk.END, "\n")

        # 添加分级标准
        text_area.insert(tk.END, "分级标准:\n")
        text_area.insert(tk.END, "-" * 50 + "\n")
        for name, min_d, max_d in self.diameter_classes:
            if max_d == float('inf'):
                text_area.insert(tk.END, f"{name}: 直径 ≥ {min_d} mm\n")
            else:
                text_area.insert(tk.END, f"{name}: {min_d} mm ≤ 直径 < {max_d} mm\n")
        text_area.insert(tk.END, "\n" + "-" * 70 + "\n\n")

        # 添加分级统计
        text_area.insert(tk.END, "分级统计结果:\n")
        text_area.insert(tk.END, "-" * 70 + "\n")

        dist = self.analyzer.root_parameters['diameter_distribution']
        for class_name, class_data in dist.items():
            if class_data['count'] > 0:
                text_area.insert(tk.END, f"{class_name}:\n")
                text_area.insert(tk.END, f"  数量: {class_data['count']}\n")
                text_area.insert(tk.END, f"  体积: {class_data['volume_mm3']:.2f} mm³\n")
                text_area.insert(tk.END, f"  体积占比: {class_data['volume_percentage']:.2f}%\n")
                text_area.insert(tk.END, f"  平均直径: {class_data['avg_diameter_mm']:.3f} mm\n")
                text_area.insert(tk.END,
                                 f"  直径范围: {class_data['min_diameter_mm']:.3f} - {class_data['max_diameter_mm']:.3f} mm\n")
                text_area.insert(tk.END, "-" * 40 + "\n\n")

        # 添加汇总信息
        text_area.insert(tk.END, "\n参数汇总:\n")
        text_area.insert(tk.END, "-" * 70 + "\n")
        text_area.insert(tk.END, f"总根系数量: {self.analyzer.root_count}\n")
        text_area.insert(tk.END, f"总根体积: {self.analyzer.root_parameters['total_volume']:.2f} mm³\n")
        text_area.insert(tk.END, f"总根长: {self.analyzer.root_parameters['total_length']:.2f} mm\n")
        text_area.insert(tk.END, f"平均根直径: {self.analyzer.root_parameters['avg_diameter']:.3f} mm\n")
        text_area.insert(tk.END, f"比根长: {self.analyzer.root_parameters['specific_root_length']:.4f} mm/mm²\n")

        # 禁用编辑
        text_area.config(state=tk.DISABLED)

        # 添加关闭按钮
        ttk.Button(detail_window, text="关闭", command=detail_window.destroy).pack(pady=10)

    def show_filter_stats(self):
        """显示过滤统计信息"""
        if not hasattr(self.analyzer, 'filter_stats'):
            messagebox.showinfo("信息", "没有过滤统计信息")
            return

        stats = self.analyzer.filter_stats

        # 创建统计窗口
        stats_window = tk.Toplevel(self.root)
        stats_window.title("过滤统计信息")
        stats_window.geometry("600x400")

        # 创建文本区域
        text_area = scrolledtext.ScrolledText(stats_window, width=70, height=20,
                                              font=("Courier New", 9))
        text_area.pack(fill=tk.BOTH, expand=True, padx=10, pady=10)

        # 添加统计信息
        text_area.insert(tk.END, "=" * 50 + "\n")
        text_area.insert(tk.END, "根系过滤统计信息\n")
        text_area.insert(tk.END, "=" * 50 + "\n\n")

        # 添加扫描优化信息
        if self.scan_optimization_enabled:
            text_area.insert(tk.END, "扫描图像优化: 已启用\n")
            if 'scan_optimized' in stats:
                text_area.insert(tk.END, "过滤方法: 扫描图像优化过滤\n")
            text_area.insert(tk.END, "\n")

        text_area.insert(tk.END, f"总区域数: {stats.get('total_regions', 0)}\n")
        text_area.insert(tk.END, f"保留区域数: {stats.get('filtered_regions', 0)}\n")
        text_area.insert(tk.END, f"过滤区域数: {stats.get('removed_regions', 0)}\n")
        text_area.insert(tk.END, f"过滤比例: {stats.get('removal_percentage', 0):.2f}%\n")

        if 'average_area' in stats:
            text_area.insert(tk.END, f"\n区域统计:\n")
            text_area.insert(tk.END, "-" * 30 + "\n")
            text_area.insert(tk.END, f"平均区域面积: {stats['average_area']:.2f} 像素\n")

        if 'average_aspect_ratio' in stats:
            text_area.insert(tk.END, f"平均纵横比: {stats['average_aspect_ratio']:.2f}\n")

        if 'filtered_min_area' in stats:
            text_area.insert(tk.END, f"\n过滤后区域统计:\n")
            text_area.insert(tk.END, "-" * 30 + "\n")
            text_area.insert(tk.END, f"最小面积: {stats['filtered_min_area']:.2f} 像素\n")
            text_area.insert(tk.END, f"最大面积: {stats['filtered_max_area']:.2f} 像素\n")
            text_area.insert(tk.END, f"平均面积: {stats['filtered_avg_area']:.2f} 像素\n")

        if 'error' in stats:
            text_area.insert(tk.END, f"\n错误信息:\n")
            text_area.insert(tk.END, "-" * 30 + "\n")
            text_area.insert(tk.END, f"{stats['error']}\n")

        # 禁用编辑
        text_area.config(state=tk.DISABLED)

        # 添加关闭按钮
        ttk.Button(stats_window, text="关闭", command=stats_window.destroy).pack(pady=10)

    def start_analysis(self):
        """开始分析单个图像"""
        if self.processing:
            messagebox.showwarning("警告", "当前正在处理中，请稍候...")
            return

        # 获取参数
        filepath = self.image_path_var.get()
        if not filepath or not os.path.exists(filepath):
            messagebox.showwarning("警告", "请先选择有效的图像文件")
            return

        output_dir = self.output_path_var.get()
        if not output_dir:
            messagebox.showwarning("警告", "请选择输出目录")
            return

        # 创建输出目录
        os.makedirs(output_dir, exist_ok=True)

        # 更新参数
        self.analyzer.pixel_to_mm = self.param_vars['pixel_to_mm'].get()

        # 更新扫描优化设置
        self.toggle_scan_optimization()

        # 启动分析线程
        self.processing = True
        self.update_status("开始分析...")

        thread = threading.Thread(
            target=self.analyze_single_image,
            args=(filepath, output_dir),
            daemon=True
        )
        thread.start()

    def batch_analysis(self):
        """批量分析多个图像"""
        if self.processing:
            messagebox.showwarning("警告", "当前正在处理中，请稍候...")
            return

        # 首先检查 batch_files 是否存在且不为空
        if not hasattr(self, 'batch_files') or not self.batch_files:
            # 如果没有批量文件，提示用户重新选择
            messagebox.showwarning("警告", "请先通过'批量选择'选择图像文件")
            return

        # 调试信息：显示选择的文件数量
        print(f"批量分析：共 {len(self.batch_files)} 个文件")
        for i, f in enumerate(self.batch_files):
            print(f"  {i + 1}: {f}")
            if not os.path.exists(f):
                print(f"    警告：文件不存在: {f}")

        output_dir = self.output_path_var.get()
        if not output_dir:
            messagebox.showwarning("警告", "请选择输出目录")
            return

        # 创建输出目录
        os.makedirs(output_dir, exist_ok=True)

        # 更新参数
        self.analyzer.pixel_to_mm = self.param_vars['pixel_to_mm'].get()

        # 更新扫描优化设置
        self.toggle_scan_optimization()

        # 启动批量分析线程
        self.processing = True
        self.update_status("开始批量分析...")

        thread = threading.Thread(
            target=self.analyze_batch_images,
            args=(self.batch_files, output_dir),
            daemon=True
        )
        thread.start()

    def parallel_batch_analysis(self):
        """并行批量分析多个图像"""
        if self.processing:
            messagebox.showwarning("警告", "当前正在处理中，请稍候...")
            return

        # 检查文件列表
        if not hasattr(self, 'batch_files') or not self.batch_files:
            messagebox.showwarning("警告", "请先通过'批量选择'选择图像文件")
            return

        # 检查输出目录
        output_dir = self.output_path_var.get()
        if not output_dir:
            messagebox.showwarning("警告", "请选择输出目录")
            return

        # 创建输出目录
        os.makedirs(output_dir, exist_ok=True)

        # 获取参数
        self.max_workers = 5  # 固定为5，限制并行处理上限
        self.batch_timeout = self.batch_timeout_var.get()

        # 更新扫描优化设置
        self.toggle_scan_optimization()

        # 更新参数
        self.analyzer.pixel_to_mm = self.param_vars['pixel_to_mm'].get()

        # 记录内存使用情况
        process = psutil.Process(os.getpid())
        memory_before = process.memory_info().rss / 1024 / 1024  # MB
        print(f"批量处理前内存使用: {memory_before:.1f} MB")

        # 启动批量分析线程
        self.processing = True
        self.update_status("开始并行批量分析...")

        thread = threading.Thread(
            target=self.analyze_parallel_batch_images,
            args=(self.batch_files, output_dir),
            daemon=True
        )
        thread.start()

    def analyze_single_image(self, image_path, output_dir):
        """分析单个图像（在线程中运行）"""
        try:
            # 步骤1: 加载图像
            self.queue_put(("status", "正在加载图像..."))
            self.queue_put(("progress", 10))

            # 应用扫描优化设置
            self.analyzer.enable_scan_optimization(self.scan_optimization_enabled)
            self.analyzer.set_scan_background_type(self.scan_background_type)
            self.analyzer.set_scan_quality(self.scan_quality)

            # 传递ROI
            self.analyzer.roi_active = self.roi_active
            self.analyzer.diameter_classes = self.diameter_classes

            success, message = self.analyzer.load_image(image_path)
            if not success:
                self.queue_put(("error", message))
                return

            # 步骤2: 分割（根据是否为扫描图像选择不同方法）
            self.queue_put(("status", "正在分割图像..."))
            self.queue_put(("progress", 30))

            success, message = self.analyzer.segment_roots(method='otsu')
            if not success:
                self.queue_put(("error", message))
                return

            # 步骤3: 过滤非根系
            self.queue_put(("status", "正在过滤非根系..."))
            self.queue_put(("progress", 50))

            success, message = self.analyzer.filter_non_roots(
                min_length=self.param_vars['min_length'].get(),
                min_area=self.param_vars['min_area'].get(),
                min_aspect_ratio=self.param_vars['min_aspect_ratio'].get()
            )
            if not success:
                self.queue_put(("warning", message))

            # 步骤4: 计数根系
            self.queue_put(("status", "正在计数根系..."))
            self.queue_put(("progress", 60))

            success, message = self.analyzer.count_roots(
                min_size=self.min_root_size_var.get()
            )
            if not success:
                self.queue_put(("warning", message))

            # 步骤5: 计算根系参数
            self.queue_put(("status", "正在计算根系参数..."))
            self.queue_put(("progress", 70))

            success, message = self.analyzer.calculate_root_parameters()
            if not success:
                self.queue_put(("warning", message))

            # 步骤6: 计算所有参数
            success, message = self.analyzer.calculate_parameters()
            if not success:
                self.queue_put(("warning", message))

            # 步骤7: 保存结果（按输出设置选项）
            self.queue_put(("status", "正在保存结果..."))
            self.queue_put(("progress", 90))

            base_name = os.path.splitext(os.path.basename(image_path))[0]
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            show_scale = self.show_scale_var.get()

            if self.save_csv_var.get():
                csv_path = os.path.join(output_dir, "根系分析结果.csv")
                success, message = self.analyzer.save_results_csv(csv_path)
                if not success:
                    self.queue_put(("warning", message))

            if self.save_json_var.get():
                json_path = os.path.join(output_dir, "根系分析结果.json")
                success, message = self.analyzer.save_results_json(json_path)
                if not success:
                    self.queue_put(("warning", message))

            if self.save_report_var.get():
                report_path = os.path.join(output_dir, f"{base_name}_详细报告_{timestamp}.png")
                success, message = self.analyzer.generate_detailed_report_image(report_path, show_scale=show_scale)
                if not success:
                    self.queue_put(("warning", message))

            if self.save_overlay_var.get():
                overlay_path = os.path.join(output_dir, f"{base_name}_结果叠加_{timestamp}.png")
                success, message = self.analyzer.export_overlay_image(overlay_path, show_scale=show_scale)
                if not success:
                    self.queue_put(("warning", message))

            # 更新UI
            self.queue_put(("result", self.analyzer.results))
            self.queue_put(("status", "分析完成！"))
            self.queue_put(("progress", 100))
            self.queue_put(("message", f"分析完成！结果已保存到:\n{output_dir}"))

            # 保存配置
            self.save_config()

        except Exception as e:
            self.queue_put(("error", f"分析过程中出错: {str(e)}\n{traceback.format_exc()}"))
        finally:
            self.processing = False

    def analyze_batch_images(self, image_paths, output_dir):
        """批量分析多个图像（在线程中运行）"""
        try:
            total = len(image_paths)
            self.queue_put(("status", f"开始批量分析，共 {total} 个图像"))

            # 检查文件是否存在
            valid_files = []
            for i, image_path in enumerate(image_paths, 1):
                if not os.path.exists(image_path):
                    self.queue_put(("warning", f"文件不存在，跳过: {image_path}"))
                    continue
                valid_files.append(image_path)

            if not valid_files:
                self.queue_put(("error", "没有有效的图像文件"))
                return

            self.queue_put(("status", f"找到 {len(valid_files)} 个有效文件"))

            for i, image_path in enumerate(valid_files, 1):
                # 更新进度
                progress = int((i - 1) / len(valid_files) * 100)
                self.queue_put(("status", f"正在处理图像 {i}/{len(valid_files)}: {os.path.basename(image_path)}"))
                self.queue_put(("progress", progress))

                # 分析单个图像
                self.analyze_single_image_in_batch(image_path, output_dir)

            # 完成
            self.queue_put(("status", "批量分析完成！"))
            self.queue_put(("progress", 100))
            self.queue_put(("message", f"批量分析完成！共处理 {len(valid_files)} 个图像\n结果已保存到:\n{output_dir}"))

            # 保存配置
            self.save_config()

        except Exception as e:
            self.queue_put(("error", f"批量分析过程中出错: {str(e)}\n{traceback.format_exc()}"))
        finally:
            self.processing = False

    def analyze_single_image_in_batch(self, image_path, output_dir):
        """批量分析中的单个图像分析"""
        try:
            # 临时分析器用于批量处理
            temp_analyzer = RootSystemAnalyzer(self.param_vars['pixel_to_mm'].get())

            # 应用扫描优化设置
            temp_analyzer.enable_scan_optimization(self.scan_optimization_enabled)
            temp_analyzer.set_scan_background_type(self.scan_background_type)
            temp_analyzer.set_scan_quality(self.scan_quality)

            # 传递ROI
            temp_analyzer.roi_active = self.roi_active
            temp_analyzer.diameter_classes = self.diameter_classes

            # 加载图像
            success, message = temp_analyzer.load_image(image_path)
            if not success:
                self.queue_put(("warning", f"跳过 {os.path.basename(image_path)}: {message}"))
                return

            # 分割
            success, message = temp_analyzer.segment_roots(method='otsu')
            if not success:
                self.queue_put(("warning", f"跳过 {os.path.basename(image_path)}: {message}"))
                return

            # 过滤
            success, message = temp_analyzer.filter_non_roots(
                min_length=self.param_vars['min_length'].get(),
                min_area=self.param_vars['min_area'].get(),
                min_aspect_ratio=self.param_vars['min_aspect_ratio'].get()
            )
            if not success:
                self.queue_put(("warning", f"跳过 {os.path.basename(image_path)}: {message}"))
                return

            # 计数根系
            success, message = temp_analyzer.count_roots(
                min_size=self.min_root_size_var.get()
            )
            if not success:
                self.queue_put(("warning", f"{os.path.basename(image_path)}: {message}"))

            # 计算根系参数
            success, message = temp_analyzer.calculate_root_parameters()
            if not success:
                self.queue_put(("warning", f"{os.path.basename(image_path)}: {message}"))

            # 计算所有参数
            success, message = temp_analyzer.calculate_parameters()
            if not success:
                self.queue_put(("warning", f"跳过 {os.path.basename(image_path)}: {message}"))
                return

            # 按输出选项保存结果
            base_name = os.path.splitext(os.path.basename(image_path))[0]
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            show_scale = self.show_scale_var.get()

            if self.save_csv_var.get():
                csv_path = os.path.join(output_dir, "根系分析结果.csv")
                temp_analyzer.save_results_csv(csv_path)

            if self.save_json_var.get():
                json_path = os.path.join(output_dir, "根系分析结果.json")
                temp_analyzer.save_results_json(json_path)

            if self.save_report_var.get():
                report_path = os.path.join(output_dir, f"{base_name}_详细报告_{timestamp}.png")
                temp_analyzer.generate_detailed_report_image(report_path, show_scale=show_scale)

            if self.save_overlay_var.get():
                overlay_path = os.path.join(output_dir, f"{base_name}_结果叠加_{timestamp}.png")
                success, message = temp_analyzer.export_overlay_image(overlay_path, show_scale=show_scale)
                if not success:
                    self.queue_put(("warning", f"生成叠加图失败: {message}"))

        except Exception as e:
            self.queue_put(("warning", f"处理 {os.path.basename(image_path)} 时出错: {str(e)}"))

    def analyze_parallel_batch_images(self, image_paths, output_dir):
        """并行批量分析多个图像（在线程中运行）"""
        try:
            total = len(image_paths)
            self.queue_put(("status", f"开始并行批量分析，共 {total} 个图像"))
            self.queue_put(("progress", 0))

            # 检查文件是否存在并准备参数
            valid_files = []
            params_list = []

            for i, image_path in enumerate(image_paths):
                if not os.path.exists(image_path):
                    self.queue_put(("warning", f"文件不存在，跳过: {image_path}"))
                    continue

                valid_files.append(image_path)

                # 准备分析参数
                params = {
                    'image_path': image_path,
                    'pixel_to_mm': self.param_vars['pixel_to_mm'].get(),
                    'seg_method': 'otsu',
                    'min_length': self.param_vars['min_length'].get(),
                    'min_area': self.param_vars['min_area'].get(),
                    'min_aspect_ratio': self.param_vars['min_aspect_ratio'].get(),
                    'min_root_size': self.min_root_size_var.get(),
                    'output_dir': output_dir,
                    'use_scan_optimization': self.scan_optimization_enabled,
                    'scan_background_type': self.scan_background_type,
                    'scan_quality': self.scan_quality,
                    'roi_active': self.roi_active,
                    'diameter_classes': self.diameter_classes
                }
                params_list.append(params)

            if not valid_files:
                self.queue_put(("error", "没有有效的图像文件"))
                return

            self.queue_put(("status", f"找到 {len(valid_files)} 个有效文件，使用 {self.max_workers} 个进程并行处理"))
            if self.scan_optimization_enabled:
                self.queue_put(("status", "扫描图像优化已启用"))

            # 清空之前的结果
            self.batch_results = []

            # 创建输出文件路径
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")
            csv_path = os.path.join(output_dir, f"根系分析结果_{timestamp}.csv")
            json_path = os.path.join(output_dir, f"根系分析结果_{timestamp}.json")

            # 准备CSV文件头
            csv_file_exists = os.path.isfile(csv_path)
            csv_headers_written = False

            # 分批处理：每批处理5个图像，避免内存占用过高
            batch_size = 5
            completed_count = 0
            failed_count = 0
            total_batches = (len(valid_files) + batch_size - 1) // batch_size

            for batch_idx in range(total_batches):
                start_idx = batch_idx * batch_size
                end_idx = min((batch_idx + 1) * batch_size, len(valid_files))
                batch_params = params_list[start_idx:end_idx]

                self.queue_put(("status", f"处理批次 {batch_idx + 1}/{total_batches} (图像 {start_idx + 1}-{end_idx})"))

                # 使用ProcessPoolExecutor进行并行处理，限制为5个进程
                with ProcessPoolExecutor(max_workers=min(5, len(batch_params))) as executor:
                    # 提交批次任务
                    future_to_params = {
                        executor.submit(RootSystemAnalyzer.analyze_single_image_static, params): params
                        for params in batch_params
                    }

                    # 处理完成的任务
                    for future in as_completed(future_to_params):
                        params = future_to_params[future]
                        image_path = params['image_path']
                        image_name = os.path.basename(image_path)

                        try:
                            # 获取结果，设置超时为660秒
                            success, result, message = future.result(timeout=self.batch_timeout)

                            if success:
                                completed_count += 1

                                # 按输出选项保存结果
                                if self.save_csv_var.get():
                                    self.save_batch_result_to_csv(result, csv_path, csv_headers_written)
                                    if not csv_headers_written:
                                        csv_headers_written = True

                                if self.save_json_var.get():
                                    self.save_batch_result_to_json(result, json_path)

                                # 生成叠加图
                                if self.save_overlay_var.get():
                                    if 'overlay_path' in result and result['overlay_path']:
                                        pass
                                    else:
                                        self.generate_batch_overlay(result, output_dir)

                                # 添加结果到列表
                                self.batch_results.append(result)

                                # 更新进度
                                progress = int(completed_count / len(valid_files) * 100)
                                self.queue_put(("status",
                                                f"完成 {completed_count}/{len(valid_files)}: {image_name}"))
                                self.queue_put(("progress", progress))

                            else:
                                failed_count += 1
                                self.queue_put(("warning",
                                                f"分析失败: {image_name} - {message}"))
                                # 更新进度（失败也计入进度）
                                progress = int((completed_count + failed_count) / len(valid_files) * 100)
                                self.queue_put(("progress", progress))

                        except TimeoutError:
                            failed_count += 1
                            self.queue_put(("warning",
                                            f"分析超时: {image_name} (超过{self.batch_timeout}秒)"))
                            progress = int((completed_count + failed_count) / len(valid_files) * 100)
                            self.queue_put(("progress", progress))

                        except Exception as e:
                            failed_count += 1
                            self.queue_put(("warning",
                                            f"分析异常: {image_name} - {str(e)}"))
                            progress = int((completed_count + failed_count) / len(valid_files) * 100)
                            self.queue_put(("progress", progress))

                        # 强制垃圾回收，释放内存
                        gc.collect()

                # 批次完成后强制垃圾回收
                gc.collect()
                time.sleep(1)  # 给系统一点时间释放内存

            # 生成批量处理汇总报告
            if completed_count > 0:
                self.generate_batch_summary_report(output_dir, timestamp)

            # 完成
            self.queue_put(("status",
                            f"批量分析完成！成功: {completed_count}, 失败: {failed_count}"))
            self.queue_put(("progress", 100))

            summary_msg = (f"批量分析完成！\n"
                           f"总文件数: {len(valid_files)}\n"
                           f"成功处理: {completed_count}\n"
                           f"处理失败: {failed_count}\n"
                           f"结果已保存到:\n{output_dir}")
            self.queue_put(("message", summary_msg))

            # 记录内存使用情况
            process = psutil.Process(os.getpid())
            memory_after = process.memory_info().rss / 1024 / 1024  # MB
            print(f"批量处理后内存使用: {memory_after:.1f} MB")

            # 保存配置
            self.save_config()

        except Exception as e:
            self.queue_put(("error",
                            f"批量分析过程中出错: {str(e)}\n{traceback.format_exc()}"))
        finally:
            self.processing = False
            # 最后强制垃圾回收
            gc.collect()

    def generate_batch_overlay(self, result, output_dir):
        """为批量处理结果生成叠加图"""
        try:
            analyzer = result['analyzer']
            base_name = os.path.splitext(result['image_name'])[0]
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

            # 生成叠加图像路径
            overlay_path = os.path.join(output_dir, f"{base_name}_结果叠加_{timestamp}.png")

            # 检查analyzer是否还有图像数据
            if (hasattr(analyzer, 'filtered_mask') and hasattr(analyzer, 'original_image') and
                    analyzer.filtered_mask is not None and analyzer.original_image is not None):

                # 使用analyzer的方法生成叠加图
                if hasattr(analyzer, 'export_overlay_image'):
                    success, message = analyzer.export_overlay_image(overlay_path)
                    if success:
                        print(f"已生成叠加图: {overlay_path}")
                        return overlay_path

                # 如果analyzer没有export_overlay_image方法，手动创建
                overlay = analyzer.original_image.copy()
                if np.sum(analyzer.filtered_mask) > 0:
                    overlay[analyzer.filtered_mask > 0] = [0, 255, 0]

                # 使用PIL绘制中文文本
                scan_info = " [扫描优化]" if result.get('use_scan_optimization', False) else ""
                info_text = f"{analyzer.image_name} | 根系数量: {analyzer.root_count}{scan_info} | {datetime.now().strftime('%Y-%m-%d %H:%M')}"
                overlay = analyzer._draw_text_pil(overlay, info_text, (10, 10), font_size=18)

                # 保存图像
                cv2.imwrite(overlay_path, overlay)
                print(f"已生成叠加图: {overlay_path}")
                return overlay_path
            else:
                print(f"警告：分析器中没有图像数据，无法生成叠加图: {result['image_name']}")
                return None

        except Exception as e:
            print(f"生成叠加图失败: {e}")
            return None

    def save_batch_result_to_csv(self, result, csv_path, headers_written):
        """保存批量处理结果到CSV文件 - 确保所有字段都存在，即使值为0"""
        try:
            # 定义所有可能的字段，确保即使值为0也保留
            all_fields = [
                '图像名称', '分析时间', '像素转换系数(mm/像素)', '图像宽度(mm)', '图像高度(mm)',
                '根系数量', '总根长(mm)', '根系面积(mm²)', '图像宽度(像素)', '图像高度(像素)',
                '最大根系面积(mm²)', '最小根系面积(mm²)', '平均根系面积(mm²)', '面积标准差(mm²)', '面积变异系数(%)',
                '最大根系长度(mm)', '最小根系长度(mm)', '平均根系长度(mm)', '长度标准差(mm)',
                '最大根系直径(mm)', '最小根系直径(mm)', '平均根系直径(mm)', '直径标准差(mm)',
                '总根系体积(mm³)', '平均根系体积(mm³)', '总根系表面积(mm²)', '平均根系表面积(mm²)',
                '总根体积(mm³)', '总根表面积(mm²)', '比根长(mm/mm²)', '总根长(累计)(mm)', '平均根直径(mm)',
            ]
            # 动态添加直径分级字段
            for class_name, _, _ in self.diameter_classes:
                all_fields.extend([
                    f'{class_name}数量', f'{class_name}体积(mm³)',
                    f'{class_name}体积占比(%)', f'{class_name}平均直径(mm)'
                ])
            all_fields.extend(['分析类型', '扫描优化'])

            # 准备数据行 - 确保所有字段都存在
            row_data = {}
            for field in all_fields:
                if field in result['results']:
                    row_data[field] = result['results'][field]
                elif field == '分析类型':
                    row_data[field] = '总体'
                elif field == '扫描优化':
                    row_data[field] = '是' if result.get('use_scan_optimization', False) else '否'
                elif field == '图像名称':
                    row_data[field] = result['image_name']
                elif field == '分析时间':
                    row_data[field] = datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                else:
                    # 对于数值字段，设置为0
                    if '数量' in field or '体积' in field or '面积' in field or '长度' in field or '直径' in field or '比根长' in field:
                        row_data[field] = 0.0
                    elif '占比' in field:
                        row_data[field] = 0.0
                    else:
                        row_data[field] = ''

            # 如果文件存在且需要写表头，或者文件不存在
            file_exists = os.path.isfile(csv_path)

            with open(csv_path, 'a', newline='', encoding='utf-8-sig') as f:
                writer = csv.DictWriter(f, fieldnames=all_fields)

                if not file_exists or not headers_written:
                    writer.writeheader()

                writer.writerow(row_data)

        except Exception as e:
            print(f"保存CSV失败: {e}")

    def save_batch_result_to_json(self, result, json_path):
        """保存批量处理结果到JSON文件"""
        try:
            # 读取现有数据或创建新列表
            data = []
            if os.path.exists(json_path):
                try:
                    with open(json_path, 'r', encoding='utf-8') as f:
                        data = json.load(f)
                except:
                    data = []

            # 创建完整结果记录
            result_record = {
                '图像信息': {
                    '文件名': result['image_name'],
                    '分析时间': datetime.now().strftime('%Y-%m-%d %H:%M:%S')
                },
                '总体结果': result['results'],
                '根系参数': result['root_parameters'],
                '过滤统计': result['filter_stats'],
                '扫描优化': result.get('use_scan_optimization', False)
            }

            # 添加新结果
            data.append(result_record)

            # 保存
            with open(json_path, 'w', encoding='utf-8') as f:
                json.dump(data, f, indent=2, ensure_ascii=False)

        except Exception as e:
            print(f"保存JSON失败: {e}")

    def generate_batch_reports(self, result, output_dir):
        """为批量处理中的单个图像生成报告和叠加图"""
        try:
            analyzer = result['analyzer']
            base_name = os.path.splitext(result['image_name'])[0]
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

            # 生成详细报告图像
            report_path = os.path.join(output_dir, f"{base_name}_详细报告_{timestamp}.png")
            if hasattr(analyzer, 'generate_detailed_report_image'):
                analyzer.generate_detailed_report_image(report_path)

            # 生成叠加图像 - 使用修复后的方法
            overlay_path = self.generate_batch_overlay(result, output_dir)
            if overlay_path:
                print(f"已生成叠加图: {overlay_path}")

        except Exception as e:
            print(f"生成报告失败: {e}")

    def generate_batch_summary_report(self, output_dir, timestamp):
        """生成批量处理汇总报告"""
        try:
            if not self.batch_results:
                return

            # 创建汇总报告文件路径
            summary_path = os.path.join(output_dir, f"批量分析汇总_{timestamp}.txt")

            with open(summary_path, 'w', encoding='utf-8') as f:
                f.write("=" * 70 + "\n")
                f.write("根系图像批量分析汇总报告\n")
                f.write("=" * 70 + "\n\n")

                f.write(f"分析时间: {datetime.now().strftime('%Y-%m-%d %H:%M:%S')}\n")
                f.write(f"处理文件总数: {len(self.batch_results)}\n")
                f.write(f"输出目录: {output_dir}\n")
                f.write(f"并行进程数: {self.max_workers}\n")
                f.write(f"超时设置: {self.batch_timeout}秒\n")
                f.write(f"扫描图像优化: {'已启用' if self.scan_optimization_enabled else '未启用'}\n")
                f.write("\n" + "-" * 70 + "\n\n")

                # 统计信息
                total_root_count = sum(r['root_count'] for r in self.batch_results)
                avg_root_count = total_root_count / len(self.batch_results) if self.batch_results else 0

                total_length = sum(r['total_length'] for r in self.batch_results)
                total_area = sum(r['total_area'] for r in self.batch_results)
                total_volume = sum(r['total_volume'] for r in self.batch_results)

                f.write("汇总统计:\n")
                f.write("-" * 40 + "\n")
                f.write(f"总根系数量: {total_root_count}\n")
                f.write(f"平均每图根系数: {avg_root_count:.2f}\n")
                f.write(f"总根长: {total_length:.2f} mm\n")
                f.write(f"总根系面积: {total_area:.2f} mm²\n")
                f.write(f"总根体积: {total_volume:.2f} mm³\n")
                f.write("\n")

                # 各图像详细信息
                f.write("各图像详细结果:\n")
                f.write("-" * 70 + "\n")

                for i, result in enumerate(self.batch_results, 1):
                    scan_info = " [扫描]" if result.get('use_scan_optimization', False) else ""
                    f.write(f"{i:3d}. {result['image_name']}{scan_info}\n")
                    f.write(f"     根系数量: {result['root_count']}\n")
                    f.write(f"     根长: {result['total_length']:.2f} mm\n")
                    f.write(f"     面积: {result['total_area']:.2f} mm²\n")
                    f.write(f"     体积: {result['total_volume']:.2f} mm³\n")

                f.write("\n" + "=" * 70 + "\n")
                f.write("报告生成完成\n")
                f.write("=" * 70 + "\n")

            # 生成统计图表
            self.generate_batch_statistics_chart(output_dir, timestamp)

        except Exception as e:
            print(f"生成汇总报告失败: {e}")

    def generate_batch_statistics_chart(self, output_dir, timestamp):
        """生成批量处理统计图表"""
        try:
            if len(self.batch_results) < 2:
                return

            import matplotlib.pyplot as plt

            # 准备数据
            image_names = [r['image_name'] for r in self.batch_results]
            root_counts = [r['root_count'] for r in self.batch_results]
            total_lengths = [r['total_length'] for r in self.batch_results]

            # 创建图表
            fig, axes = plt.subplots(2, 2, figsize=(14, 10))
            fig.suptitle(f'批量分析统计图表 - {timestamp}', fontsize=16, fontweight='bold')

            # 1. 根系数量柱状图
            ax1 = axes[0, 0]
            bars1 = ax1.bar(range(len(image_names)), root_counts, color='skyblue')
            ax1.set_title('各图像根系数量分布', fontsize=12)
            ax1.set_xlabel('图像序号')
            ax1.set_ylabel('根系数量')
            ax1.set_xticks(range(len(image_names)))
            ax1.set_xticklabels([str(i + 1) for i in range(len(image_names))], rotation=45)

            # 添加数值标签
            for bar in bars1:
                height = bar.get_height()
                ax1.text(bar.get_x() + bar.get_width() / 2., height + 0.1,
                         f'{int(height)}', ha='center', va='bottom', fontsize=9)

            # 2. 总根长柱状图
            ax2 = axes[0, 1]
            bars2 = ax2.bar(range(len(image_names)), total_lengths, color='lightgreen')
            ax2.set_title('各图像总根长分布', fontsize=12)
            ax2.set_xlabel('图像序号')
            ax2.set_ylabel('总根长 (mm)')
            ax2.set_xticks(range(len(image_names)))
            ax2.set_xticklabels([str(i + 1) for i in range(len(image_names))], rotation=45)

            # 3. 根系数量分布直方图
            ax3 = axes[1, 0]
            ax3.hist(root_counts, bins=min(10, len(set(root_counts))),
                     color='lightcoral', edgecolor='black', alpha=0.7)
            ax3.set_title('根系数量分布直方图', fontsize=12)
            ax3.set_xlabel('根系数量')
            ax3.set_ylabel('频数')

            # 4. 总根长分布直方图
            ax4 = axes[1, 1]
            ax4.hist(total_lengths, bins=min(10, len(set(total_lengths))),
                     color='gold', edgecolor='black', alpha=0.7)
            ax4.set_title('总根长分布直方图', fontsize=12)
            ax4.set_xlabel('总根长 (mm)')
            ax4.set_ylabel('频数')

            plt.tight_layout(rect=[0, 0, 1, 0.96])

            # 保存图表
            chart_path = os.path.join(output_dir, f"批量分析统计图表_{timestamp}.png")
            plt.savefig(chart_path, dpi=150, bbox_inches='tight')
            plt.close()

        except Exception as e:
            print(f"生成统计图表失败: {e}")
            # 如果matplotlib不可用，静默失败

    def export_result_image(self):
        """导出结果图像"""
        if not hasattr(self.analyzer, 'filtered_mask'):
            messagebox.showwarning("警告", "请先进行分析")
            return

        # 选择保存目录
        initial_dir = self.output_path_var.get() if self.output_path_var.get() else None

        dirpath = filedialog.askdirectory(
            title="选择图像保存目录",
            initialdir=initial_dir
        )

        if not dirpath:
            return

        try:
            base_name = os.path.splitext(os.path.basename(self.current_image_path))[0] if self.current_image_path else "export"
            timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

            # 弹出选项对话框
            options_window = tk.Toplevel(self.root)
            options_window.title("选择导出图像")
            options_window.geometry("300x230")
            options_window.transient(self.root)
            options_window.grab_set()

            ttk.Label(options_window, text="请选择要导出的图像类型:",
                     font=("Arial", 10, "bold")).pack(pady=(15, 10))

            export_overlay_var = tk.BooleanVar(value=True)
            export_report_var = tk.BooleanVar(value=False)
            show_scale_var = tk.BooleanVar(value=True)

            ttk.Checkbutton(options_window, text="叠加图像 (根系标记)",
                           variable=export_overlay_var).pack(anchor=tk.W, padx=30, pady=(0, 3))
            ttk.Checkbutton(options_window, text="详细报告图 (参数汇总)",
                           variable=export_report_var).pack(anchor=tk.W, padx=30, pady=(0, 3))
            ttk.Separator(options_window, orient='horizontal').pack(fill=tk.X, padx=20, pady=8)
            ttk.Checkbutton(options_window, text="图像中显示比例尺",
                           variable=show_scale_var).pack(anchor=tk.W, padx=30, pady=(0, 10))

            def do_export():
                options_window.destroy()

                if not export_overlay_var.get() and not export_report_var.get():
                    messagebox.showwarning("警告", "请至少选择一种图像类型")
                    return

                exported = []
                if export_overlay_var.get():
                    overlay_path = os.path.join(dirpath, f"{base_name}_叠加_{timestamp}.png")
                    success, msg = self.analyzer.export_overlay_image(overlay_path, show_scale=show_scale_var.get())
                    if success:
                        exported.append(f"叠加图像: {os.path.basename(overlay_path)}")
                    else:
                        messagebox.showerror("错误", msg)
                        return

                if export_report_var.get():
                    report_path = os.path.join(dirpath, f"{base_name}_报告_{timestamp}.png")
                    success, msg = self.analyzer.generate_detailed_report_image(report_path, show_scale=show_scale_var.get())
                    if success:
                        exported.append(f"报告图像: {os.path.basename(report_path)}")
                    else:
                        messagebox.showerror("错误", msg)
                        return

                self.update_status(f"图像已导出到: {dirpath}")
                messagebox.showinfo("导出成功", "已导出以下图像:\n\n" + "\n".join(exported))

            btn_frame = ttk.Frame(options_window)
            btn_frame.pack(pady=10)
            ttk.Button(btn_frame, text="导出", command=do_export).pack(side=tk.LEFT, padx=5)
            ttk.Button(btn_frame, text="取消", command=options_window.destroy).pack(side=tk.LEFT, padx=5)

        except Exception as e:
            messagebox.showerror("错误", f"导出失败: {str(e)}")

    def export_results(self):
        """导出结果数据"""
        if not hasattr(self.analyzer, 'results') or not self.analyzer.results:
            messagebox.showwarning("警告", "没有可导出的分析结果")
            return

        # 选择保存位置
        filetypes = [
            ('CSV文件', '*.csv'),
            ('JSON文件', '*.json'),
            ('文本文件', '*.txt'),
            ('所有文件', '*.*')
        ]

        initial_dir = self.output_path_var.get() if self.output_path_var.get() else None

        filepath = filedialog.asksaveasfilename(
            title="导出分析结果",
            defaultextension=".csv",
            filetypes=filetypes,
            initialdir=initial_dir
        )

        if filepath:
            try:
                ext = os.path.splitext(filepath)[1].lower()

                if ext == '.csv':
                    # 导出为CSV - 包含所有参数
                    with open(filepath, 'w', newline='', encoding='utf-8-sig') as f:
                        # 导出总体结果
                        writer = csv.DictWriter(f, fieldnames=self.analyzer.results.keys())
                        writer.writeheader()
                        writer.writerow(self.analyzer.results)
                    message = "CSV文件导出成功（包含所有根系参数）"

                elif ext == '.json':
                    # 导出为JSON
                    with open(filepath, 'w', encoding='utf-8') as f:
                        json.dump(self.analyzer.results, f, indent=2, ensure_ascii=False)
                    message = "JSON文件导出成功"

                elif ext == '.txt':
                    # 导出为文本
                    with open(filepath, 'w', encoding='utf-8') as f:
                        f.write("=" * 60 + "\n")
                        f.write("根系分析结果报告\n")
                        f.write("=" * 60 + "\n\n")
                        f.write(f"图像名称: {self.analyzer.results.get('图像名称', '')}\n")
                        f.write(f"分析时间: {self.analyzer.results.get('分析时间', '')}\n")
                        if self.scan_optimization_enabled:
                            f.write(f"扫描优化: 已启用\n")
                        f.write("-" * 60 + "\n\n")

                        f.write("基本参数:\n")
                        basic_params = ['根系数量', '总根长(mm)', '根系面积(mm²)',
                                        '总根体积(mm³)', '总根表面积(mm²)', '平均根直径(mm)']
                        for param in basic_params:
                            if param in self.analyzer.results:
                                f.write(f"  {param}: {self.analyzer.results[param]}\n")

                        f.write("\n衍生参数:\n")
                        derived_params = ['比根长(mm/mm²)']
                        for param in derived_params:
                            if param in self.analyzer.results:
                                f.write(f"  {param}: {self.analyzer.results[param]}\n")

                        # 添加直径分级信息
                        if hasattr(self.analyzer,
                                   'root_parameters') and 'diameter_distribution' in self.analyzer.root_parameters:
                            f.write("\n" + "=" * 60 + "\n")
                            f.write("根系直径分级结果\n")
                            f.write("=" * 60 + "\n\n")

                            dist = self.analyzer.root_parameters['diameter_distribution']
                            for class_name, class_data in dist.items():
                                if class_data['count'] > 0:
                                    f.write(f"{class_name}:\n")
                                    f.write(f"  数量: {class_data['count']}\n")
                                    f.write(f"  体积: {class_data['volume_mm3']:.2f} mm³\n")
                                    f.write(f"  体积占比: {class_data['volume_percentage']:.2f}%\n")
                                    f.write(f"  平均直径: {class_data['avg_diameter_mm']:.3f} mm\n")
                                    f.write("-" * 40 + "\n")

                    message = "文本文件导出成功"

                else:
                    message = "不支持的格式"

                self.update_status(message)
                messagebox.showinfo("成功", f"{message}\n文件已保存到:\n{filepath}")

            except Exception as e:
                messagebox.showerror("错误", f"导出失败: {str(e)}")

    def copy_results(self):
        """复制结果到剪贴板"""
        try:
            # 获取结果文本
            result_text = self.result_text.get(1.0, tk.END).strip()
            if result_text:
                self.root.clipboard_clear()
                self.root.clipboard_append(result_text)
                self.update_status("结果已复制到剪贴板")
        except Exception as e:
            messagebox.showerror("错误", f"复制失败: {str(e)}")

    def load_config(self):
        """加载配置"""
        config_file = "config.json"
        if os.path.exists(config_file):
            try:
                with open(config_file, 'r', encoding='utf-8') as f:
                    config = json.load(f)

                if 'output_dir' in config:
                    self.output_path_var.set(config['output_dir'])
                if 'image_path' in config:
                    self.image_path_var.set(config['image_path'])
                if 'pixel_to_mm' in config:
                    self.param_vars['pixel_to_mm'].set(config['pixel_to_mm'])
                if 'min_length' in config:
                    self.param_vars['min_length'].set(config['min_length'])
                if 'min_area' in config:
                    self.param_vars['min_area'].set(config['min_area'])
                if 'min_aspect_ratio' in config:
                    self.param_vars['min_aspect_ratio'].set(config['min_aspect_ratio'])
                if 'min_root_size' in config:
                    self.min_root_size_var.set(config['min_root_size'])
                if 'known_length' in config:
                    self.known_length_var.set(config['known_length'])
                if 'pixel_length' in config:
                    self.pixel_length_var.set(config['pixel_length'])
                if 'image_width_mm' in config:
                    self.image_width_mm_var.set(config['image_width_mm'])
                if 'image_height_mm' in config:
                    self.image_height_mm_var.set(config['image_height_mm'])
                if 'scan_optimization' in config:
                    self.scan_optimization_var.set(config['scan_optimization'])
                if 'scan_background_type' in config:
                    self.scan_background_type_var.set(config['scan_background_type'])
                if 'scan_quality' in config:
                    self.scan_quality_var.set(config['scan_quality'])
                if 'max_workers' in config:
                    self.max_workers_var.set(5)  # 固定为5
                if 'batch_timeout' in config:
                    self.batch_timeout_var.set(config['batch_timeout'])

                if 'diameter_classes' in config:
                    try:
                        loaded = config['diameter_classes']
                        self.diameter_classes = [
                            (name, float(min_v), float('inf') if max_v == -1 else float(max_v))
                            for name, min_v, max_v in loaded
                        ]
                        if len(self.diameter_classes) < 2:
                            self.diameter_classes = list(RootSystemAnalyzer.DEFAULT_DIAMETER_CLASSES)
                    except Exception:
                        self.diameter_classes = list(RootSystemAnalyzer.DEFAULT_DIAMETER_CLASSES)

                # 应用扫描优化设置
                self.toggle_scan_optimization()

            except Exception as e:
                print(f"加载配置失败: {e}")

    def save_config(self):
        """保存配置"""
        config = {
            'output_dir': self.output_path_var.get(),
            'image_path': self.image_path_var.get(),
            'pixel_to_mm': self.param_vars['pixel_to_mm'].get(),
            'min_length': self.param_vars['min_length'].get(),
            'min_area': self.param_vars['min_area'].get(),
            'min_aspect_ratio': self.param_vars['min_aspect_ratio'].get(),
            'min_root_size': self.min_root_size_var.get(),
            'known_length': self.known_length_var.get(),
            'pixel_length': self.pixel_length_var.get(),
            'image_width_mm': self.image_width_mm_var.get(),
            'image_height_mm': self.image_height_mm_var.get(),
            'scan_optimization': self.scan_optimization_enabled,
            'scan_background_type': self.scan_background_type,
            'scan_quality': self.scan_quality,
            'max_workers': 5,  # 固定为5
            'batch_timeout': self.batch_timeout_var.get(),
            'diameter_classes': [
                [name, min_val, -1 if max_val == float('inf') else max_val]
                for name, min_val, max_val in self.diameter_classes
            ]
        }

        try:
            with open("config.json", 'w', encoding='utf-8') as f:
                json.dump(config, f, indent=2, ensure_ascii=False)
        except Exception as e:
            print(f"保存配置失败: {e}")

    def queue_put(self, item):
        """向队列添加项目"""
        self.queue.put(item)

    def process_queue(self):
        """处理队列中的项目"""
        try:
            while True:
                item = self.queue.get_nowait()
                item_type, value = item

                if item_type == "status":
                    self.update_status(value)
                elif item_type == "progress":
                    self.progress_var.set(value)
                elif item_type == "result":
                    self.display_results(value)
                elif item_type == "message":
                    messagebox.showinfo("完成", value)
                elif item_type == "warning":
                    messagebox.showwarning("警告", value)
                elif item_type == "error":
                    messagebox.showerror("错误", value)
                    self.processing = False

        except queue.Empty:
            pass
        finally:
            self.root.after(100, self.process_queue)

    def update_status(self, message):
        """更新状态栏"""
        self.status_var.set(message)
        self.root.update_idletasks()

    def display_results(self, results):
        """显示分析结果"""
        self.result_text.delete(1.0, tk.END)

        # 添加标题
        self.result_text.insert(tk.END, "=" * 40 + "\n")
        self.result_text.insert(tk.END, "根系分析结果\n")
        self.result_text.insert(tk.END, "=" * 40 + "\n\n")

        # 添加扫描优化信息
        if self.scan_optimization_enabled:
            self.result_text.insert(tk.END, "扫描图像优化: 已启用\n")
            self.result_text.insert(tk.END, f"背景类型: {self.analyzer.scan_params['background_type']}\n")
            self.result_text.insert(tk.END, f"扫描质量: {self.analyzer.scan_params['scan_quality']}\n")
            self.result_text.insert(tk.END, "\n")

        # 添加基本参数
        self.result_text.insert(tk.END, "基本参数:\n")
        self.result_text.insert(tk.END, "-" * 30 + "\n")

        basic_keys = ['图像名称', '分析时间', '像素转换系数(mm/像素)',
                      '图像宽度(mm)', '图像高度(mm)', '根系数量']

        for key in basic_keys:
            if key in results:
                self.result_text.insert(tk.END, f"{key}: {results[key]}\n")

        self.result_text.insert(tk.END, "\n尺寸参数:\n")
        self.result_text.insert(tk.END, "-" * 30 + "\n")

        size_keys = ['总根长(mm)', '根系面积(mm²)', '总根体积(mm³)',
                     '总根表面积(mm²)', '平均根直径(mm)']

        for key in size_keys:
            if key in results:
                self.result_text.insert(tk.END, f"{key}: {results[key]}\n")

        self.result_text.insert(tk.END, "\n衍生参数:\n")
        self.result_text.insert(tk.END, "-" * 30 + "\n")

        derived_keys = ['比根长(mm/mm²)']

        for key in derived_keys:
            if key in results:
                self.result_text.insert(tk.END, f"{key}: {results[key]}\n")

        # 添加直径分级信息
        if any(key.endswith('体积占比(%)') for key in results.keys()):
            self.result_text.insert(tk.END, "\n直径分级体积占比:\n")
            self.result_text.insert(tk.END, "-" * 30 + "\n")

            for class_name, _, _ in self.diameter_classes:
                volume_key = f'{class_name}体积占比(%)'
                count_key = f'{class_name}数量'
                if volume_key in results:
                    self.result_text.insert(tk.END,
                                            f"{class_name}: {results.get(count_key, 0)}个, {results[volume_key]}%\n")

        # 添加尺寸分布信息
        if '最大根系面积(mm²)' in results:
            self.result_text.insert(tk.END, "\n尺寸分布:\n")
            self.result_text.insert(tk.END, "-" * 30 + "\n")

            distribution_keys = ['最大根系面积(mm²)', '最小根系面积(mm²)',
                                 '平均根系面积(mm²)', '面积标准差(mm²)',
                                 '最大根系长度(mm)', '最小根系长度(mm)',
                                 '平均根系长度(mm)']

            for key in distribution_keys:
                if key in results:
                    self.result_text.insert(tk.END, f"{key}: {results[key]}\n")

        # 更新图像预览
        self.show_image('结果图')


def main():
    """主函数"""
    # 设置多进程的启动方式为spawn，避免fork问题
    if sys.platform.startswith('win'):
        multiprocessing.freeze_support()
    else:
        multiprocessing.set_start_method('spawn', force=True)

    # 检查Python版本
    python_version = sys.version_info
    print(f"Python版本: {python_version.major}.{python_version.minor}.{python_version.micro}")
    print(f"CPU核心数: {multiprocessing.cpu_count()}")
    print(f"并行处理超时时间: 660秒")
    print(f"并行处理上限: 5张图片")
    print(f"扫描图像优化: 已集成")

    # 创建主窗口
    root = tk.Tk()

    # 创建应用程序
    app = RootAnalysisApp(root)

    # 窗口关闭时保存配置
    def on_closing():
        app.save_config()
        root.destroy()

    root.protocol("WM_DELETE_WINDOW", on_closing)

    # 运行主循环
    root.mainloop()


if __name__ == "__main__":
    main()